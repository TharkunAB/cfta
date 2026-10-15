{-# LANGUAGE OverloadedStrings #-}

{- | The streamed walk of "Data.CFTA.GHC.Fits" end to end, on five easy
Hoogle+ queries and five queries of higher-kinded types with the Prelude:
each query gives its expected program, or a fit with its normal form, and
GHC accepts every fit as a program of the query's signature. Also: the
fits that ignore an argument are marked, the walk leaves the goal's
unification variables as it found them, and the fast rejects keep three
fits that only the solver can decide (a coercion through a newtype, a given
equality, and a quantified given). The normal forms merge the fits that
respell one program, as @flip filter xs p@ and @filter p xs@, keep the fits
that differ in meaning, and mark the fits that drop an argument.
-}
module Main (main) where

import Control.Monad (forM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as Text
import Test.Hspec (describe, hspec, it, shouldBe, shouldReturn, shouldSatisfy)

import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.Internal.Check (Leaf (..), complete, newEnvironment, startWalker, step)
import Data.CFTA.GHC.Session
import Data.CFTA.Gen.Synthesis (Program (..), parseProgram, renderProgram)
import Data.CFTA.Gen.Synthesis.Walk (preorder)
import GHC.Builtin.Types (mkListTy)
import GHC.Core.Type (liftedTypeKind, mkTyVarTy)
import GHC.Data.Bag (emptyBag)
import GHC.Tc.Utils.TcMType (newFlexiTyVar, readMetaTyVar)
import GHC.Tc.Utils.TcType (isFlexi)

-- | A query: its name, its signature, its argument names, and the expected program.
data Query = Query String String [Text] Program

-- | Five easy Hoogle+ queries; @mergeEither@ has three component leaves.
queries :: [Query]
queries =
    [ query "map" "(a -> b) -> [a] -> [b]" ["f", "xs"] "map f xs"
    , query "firstKey" "[(a, b)] -> a" ["xs"] "fst (head xs)"
    , query "singletonList" "a -> [a]" ["x"] "(:) x []"
    , query "resolveEither" "Either a b -> (a -> b) -> b" ["e", "f"] "either f id e"
    , query "mergeEither" "Either a (Either a b) -> Either a b" ["e"] "either Left id e"
    ]
  where
    query name signature arguments expected = Query name signature arguments (either error id (parseProgram expected))

{- | Queries of higher-kinded types, which need the specializations of
@fmap@, @(>>=)@, and @pure@ at the type heads of the query, under the
signature's givens or by the instances in scope.
-}
higherKinded :: [Query]
higherKinded =
    [ query "join" "Monad m => m (m a) -> m a" ["x"] "(>>=) x id"
    , query "fmapFst" "Functor f => f (a, b) -> f a" ["x"] "fmap fst x"
    , query "joinMaybe" "Maybe (Maybe a) -> Maybe a" ["x"] "(>>=) x id"
    , query "bind" "Monad m => (a -> m b) -> m a -> m b" ["f", "x"] "(>>=) x f"
    , query "pureSingleton" "Applicative f => a -> f [a]" ["x"] "pure ((:) x [])"
    ]
  where
    query name signature arguments expected = Query name signature arguments (either error id (parseProgram expected))

main :: IO ()
main = withSession ["import Prelude", "import Data.Coerce (coerce)", "import Data.Monoid (Sum (..))"] $ \session -> do
    candidates <- candidatesOf session [Import "Prelude" Nothing]
    -- The modules of base with the other components of the laws.
    others <-
        candidatesOf
            session
            [Import name Nothing | name <- ["Data.Tuple", "Data.Function", "Data.Bool", "Data.Maybe", "Data.Either", "Data.List"]]
    coercions <- candidatesOf session [Import "Data.Coerce" Nothing]
    declare session "class Sized a where { sized :: a -> Int }; instance Sized Int where { sized = id }"
    Just sizedType <- typeOfExpression session "sized"
    let
        -- Whether one program fits a signature, by the steps of the walk.
        checks signature arguments program = do
            Just typ <- typeOfExpression session ("undefined :: " <> signature)
            let extra = coercions <> [Candidate "sized" sizedType True False Nothing]
            inSignatureHole session (candidates <> extra) typ arguments $ \hole candidates' goal -> do
                environment <- newEnvironment hole
                let leaves = Map.fromList [(candidateName c, Leaf (candidateName c) (candidateType c) (candidateHeads c)) | c <- candidates']
                    go walker [] = complete environment walker
                    go walker ((name, children) : rest) = case Map.lookup name leaves of
                        Just leaf -> step environment walker leaf children False >>= maybe (pure False) (`go` rest)
                        Nothing -> pure False
                go (startWalker environment (map candidateType candidates') goal) (preorder program)
    hspec $ do
        describe "streamFits" $
            forM_ (queries <> higherKinded) $ \(Query name signature arguments expected) ->
                it ("finds the expected program of " <> name <> ", and GHC accepts its fits") $ do
                    Just typ <- typeOfExpression session ("undefined :: " <> signature)
                    Just normal <- inTypechecker session (normalFormsOf candidates)
                    found <- newIORef []
                    let options = defaultOptions{optionMaximumSize = size expected}
                        -- The expected program, or an earlier fit with its normal form.
                        isExpected program = program == expected || (isJust (normal expected) && normal program == normal expected)
                        record fit = do
                            liftIO (modifyIORef' found (fitProgram fit :))
                            pure (not (isExpected (fitProgram fit)))
                    statistics <- fitsForSignature session options candidates typ arguments record
                    fits <- reverse <$> readIORef found
                    fmap statisticsFits statistics `shouldBe` Just (length fits)
                    fits `shouldSatisfy` any isExpected
                    forM_ (take 10 fits) $ \fit ->
                        accepts session ("(\\" <> unwords (map Text.unpack arguments) <> " -> " <> renderProgram fit <> ") :: " <> signature)
                            `shouldReturn` True
        describe "fitIgnoresPart" $
            it "marks the fits that ignore an argument" $ do
                marks <- forM ignoring $ \(signature, arguments, programs) -> do
                    Just typ <- typeOfExpression session ("undefined :: " <> signature)
                    found <- newIORef []
                    let wanted = map parse programs
                        record fit = liftIO $ do
                            modifyIORef' found (fit :)
                            fits <- readIORef found
                            pure (not (all (`elem` map fitProgram fits) wanted))
                    _ <-
                        fitsForSignature
                            session
                            defaultOptions{optionMaximumSize = 4, optionNormalForms = False}
                            candidates
                            typ
                            arguments
                            record
                    fits <- readIORef found
                    pure [lookup program [(fitProgram fit, fitIgnoresPart fit) | fit <- fits] | program <- wanted]
                marks `shouldBe` [[Just True, Just False], [Just True, Just False]]
        describe "normal forms" $ do
            it "unfold each component of base with a body, one law each" $ do
                Just normal <- inTypechecker session (normalFormsOf (candidates <> others))
                let holds (left, right) = isJust (normal (parse left)) && normal (parse left) == normal (parse right)
                filter (not . holds) laws `shouldBe` []
                -- listToMaybe is foldr, which is recursive, so it does not reduce on a list.
                holds ("listToMaybe ((:) x xs)", "Just x") `shouldBe` False
            it "merge the respellings of one program, and keep the programs that differ" $ do
                Just normal <- inTypechecker session (normalFormsOf candidates)
                let same left right = isJust (normal (parse left)) && normal (parse left) == normal (parse right)
                map (uncurry same) respellings `shouldBe` map (const True) respellings
                map (uncurry same) different `shouldBe` map (const False) different
            it "skip a fit with the normal form of an earlier fit, behind an option" $ do
                Just typ <- typeOfExpression session "undefined :: (a -> Bool) -> [a] -> [a]"
                let fitsWith normalForms = do
                        found <- newIORef []
                        let record fit = True <$ liftIO (modifyIORef' found (fitProgram fit :))
                            options = defaultOptions{optionMaximumSize = 4, optionNormalForms = normalForms}
                        statistics <- fitsForSignature session options candidates typ ["p", "xs"] record
                        fits <- readIORef found
                        pure (fits, maybe 0 statisticsMerged statistics)
                (merged, skipped) <- fitsWith True
                (unmerged, _) <- fitsWith False
                merged `shouldSatisfy` elem (parse "filter p xs")
                merged `shouldSatisfy` notElem (parse "flip filter xs p")
                unmerged `shouldSatisfy` elem (parse "flip filter xs p")
                skipped `shouldSatisfy` (> 0)
                length merged + skipped `shouldBe` length unmerged
            it "mark a fit whose normal form drops an argument" $ do
                Just typ <- typeOfExpression session "undefined :: [a] -> Int -> [a]"
                found <- newIORef []
                -- const xs n is xs, by the body of const.
                let wanted = map parse ["const xs n", "take n xs"]
                    record fit = liftIO $ do
                        modifyIORef' found (fit :)
                        fits <- readIORef found
                        pure (not (all (`elem` map fitProgram fits) wanted))
                _ <- fitsForSignature session defaultOptions{optionMaximumSize = 4} candidates typ ["xs", "n"] record
                fits <- readIORef found
                [lookup program [(fitProgram fit, fitDropsArgument fit) | fit <- fits] | program <- wanted]
                    `shouldBe` [Just True, Just False]
        describe "the fast rejects" $
            forM_ soundness $ \(name, signature, arguments, program) ->
                it ("keep the fit of " <> name) $
                    checks signature arguments (parse program) `shouldReturn` Just True
        describe "synthesizeFits" $
            it "leaves the unification variables of the goal as it found them" $ do
                result <- inTypechecker session $ do
                    variable <- newFlexiTyVar liftedTypeKind
                    let hole = TypedHole{th_relevant_cts = emptyBag, th_implics = [], th_hole = Nothing}
                    fits <-
                        synthesizeFits
                            defaultOptions{optionMaximumSize = 2, optionFits = 3}
                            hole
                            candidates
                            (mkListTy (mkTyVarTy variable))
                    details <- readMetaTyVar variable
                    pure (length fits, isFlexi details)
                result `shouldBe` Just (3, True)
  where
    -- Two signatures, each with a fit that ignores an argument and one that does not.
    ignoring =
        [ ("[a] -> Int -> [a]", ["xs", "n"], ["const xs n", "take n xs"])
        , ("(a -> Bool) -> [a] -> Int", ["p", "xs"], ["const (length xs) p", "length (filter p xs)"])
        ]
    -- Fits that the solver accepts and a careless fast reject would not.
    soundness =
        [ ("a coercion through a newtype", "[Sum Int] -> [Int]", ["xs"], "coerce xs")
        , ("a given equality", "(a ~ Int) => a -> Int", ["x"], "x")
        , ("a quantified given", "(forall x. Sized (f x)) => f Bool -> Int", ["y"], "sized y")
        ]
    {- One law for each component of base that has a body from its unfolding
    in GHC 9.14 (the constructors of pairs, lists, Bool, Maybe, and Either
    occur in them). A GHC release that drops or changes an unfolding breaks
    its law.
    -}
    laws =
        [ ("fst ((,) x y)", "x")
        , ("snd ((,) x y)", "y")
        , ("curry f x y", "f ((,) x y)")
        , ("uncurry f ((,) x y)", "f x y")
        , ("swap ((,) x y)", "(,) y x")
        , ("id x", "x")
        , ("const x y", "x")
        , ("flip f x y", "f y x")
        , ("(.) f g x", "f (g x)")
        , ("($) f x", "f x")
        , ("(&) x f", "f x")
        , ("on g f x y", "g (f x) (f y)")
        , ("otherwise", "True")
        , ("not True", "False")
        , ("(&&) True b", "b")
        , ("(||) False b", "b")
        , ("bool f t True", "t")
        , ("maybe n f (Just x)", "f x")
        , ("fromMaybe d (Just x)", "x")
        , ("isJust (Just x)", "True")
        , ("isNothing Nothing", "True")
        , ("fromJust (Just x)", "x")
        , ("maybeToList (Just x)", "(:) x []")
        , ("either f g (Left x)", "f x")
        , ("fromLeft d (Left x)", "x")
        , ("fromRight d (Right x)", "x")
        , ("isLeft (Left x)", "True")
        , ("isRight (Right x)", "True")
        , ("head ((:) x xs)", "x")
        , ("tail ((:) x xs)", "xs")
        , ("uncons ((:) x xs)", "Just ((,) x xs)")
        ]
    -- Programs that respell one program, from the probe of the merges.
    respellings =
        [ ("flip filter xs p", "filter p xs")
        , ("curry snd n (f x)", "f x")
        , ("(.) length reverse xs", "length (reverse xs)")
        , ("uncurry id p", "fst p (snd p)")
        , ("maybe n f (Just x)", "f x")
        , ("either f g (Left x)", "f x")
        , ("(,) (fst p) (snd p)", "p")
        , ("not (not b)", "b")
        , -- Unsaturated components with a body merge by eta-expansion.
          ("foldr (flip const) z xs", "foldr (const id) z xs")
        ]
    -- Programs that differ in meaning.
    different =
        [ ("filter p xs", "takeWhile p xs")
        , ("fst p", "snd p")
        , ("flip f x y", "f x y")
        , ("maybe n f m", "f m")
        ]
    parse = either error id . parseProgram
    size program = case program of
        Var _ -> 1
        App function argument -> size function + size argument
