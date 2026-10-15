{-# LANGUAGE OverloadedStrings #-}

{- | The streamed walk of "Data.CFTA.GHC.Fits" end to end, on five easy
Hoogle+ queries and five queries of higher-kinded types with the Prelude:
each query gives its expected program, and GHC accepts every fit as a
program of the query's signature. Also: the
fits that ignore an argument are marked, the walk leaves the goal's
unification variables as it found them, and the fast rejects keep three
fits that only the solver can decide (a coercion through a newtype, a given
equality, and a quantified given).
-}
module Main (main) where

import Control.Monad (forM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
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
    coercions <- candidatesOf session [Import "Data.Coerce" Nothing]
    declare session "class Sized a where { sized :: a -> Int }; instance Sized Int where { sized = id }"
    Just sizedType <- typeOfExpression session "sized"
    let
        -- Whether one program fits a signature, by the steps of the walk.
        checks signature arguments program = do
            Just typ <- typeOfExpression session ("undefined :: " <> signature)
            let extra = coercions <> [Candidate "sized" sizedType True False]
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
            forM_ [(False, ""), (True, ", with the domains of kind Type")] $ \(domains, label) ->
                forM_ (queries <> higherKinded) $ \(Query name signature arguments expected) ->
                    it ("finds the expected program of " <> name <> ", and GHC accepts its fits" <> label) $ do
                        Just typ <- typeOfExpression session ("undefined :: " <> signature)
                        found <- newIORef []
                        let options = defaultOptions{optionMaximumSize = size expected, optionTypeDomains = domains}
                            record fit = do
                                liftIO (modifyIORef' found (fitProgram fit :))
                                pure (fitProgram fit /= expected)
                        statistics <- fitsForSignature session options candidates typ arguments record
                        fits <- reverse <$> readIORef found
                        fmap statisticsFits statistics `shouldBe` Just (length fits)
                        fits `shouldSatisfy` elem expected
                        forM_ (take 10 fits) $ \fit ->
                            accepts session ("(\\" <> unwords (map Text.unpack arguments) <> " -> " <> renderProgram fit <> ") :: " <> signature)
                                `shouldReturn` True
        describe "optionTypeDomains" $
            it "proposes no maximum at a rigid goal without a given Ord, and keeps head" $ do
                Just typ <- typeOfExpression session "undefined :: [a] -> a"
                let proposed domains = do
                        traced <- newIORef []
                        let options =
                                defaultOptions
                                    { optionMaximumSize = 2
                                    , optionTypeDomains = domains
                                    , optionTrace = Just (\_ program -> modifyIORef' traced (program :))
                                    }
                        _ <- fitsForSignature session options candidates typ ["xs"] (\_ -> pure True)
                        readIORef traced
                without <- proposed False
                with <- proposed True
                (parse "maximum xs" `elem` without, parse "maximum xs" `elem` with, parse "head xs" `elem` with)
                    `shouldBe` (True, False, True)
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
                    _ <- fitsForSignature session defaultOptions{optionMaximumSize = 4} candidates typ arguments record
                    fits <- readIORef found
                    pure [lookup program [(fitProgram fit, fitIgnoresPart fit) | fit <- fits] | program <- wanted]
                marks `shouldBe` [[Just True, Just False], [Just True, Just False]]
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
    parse = either error id . parseProgram
    size program = case program of
        Var _ -> 1
        App function argument -> size function + size argument
