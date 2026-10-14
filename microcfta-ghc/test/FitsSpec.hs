{-# LANGUAGE OverloadedStrings #-}

{- | The streamed walk of "Data.CFTA.GHC.Fits" end to end, on five easy
Hoogle+ queries with the Prelude: each query gives its expected program,
and GHC accepts every fit as a program of the query's signature. Also: the
fits that ignore an argument are marked, and the walk leaves the goal's
unification variables as it found them.
-}
module Main (main) where

import Control.Monad (forM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Text (Text)
import qualified Data.Text as Text
import Test.Hspec (describe, hspec, it, shouldBe, shouldReturn, shouldSatisfy)

import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.Session
import Data.CFTA.Gen.Synthesis (Program (..), parseProgram, renderProgram)
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

main :: IO ()
main = withSession ["import Prelude"] $ \session -> do
    candidates <- candidatesOf session [Import "Prelude" Nothing]
    hspec $ do
        describe "streamFits" $
            forM_ queries $ \(Query name signature arguments expected) ->
                it ("finds the expected program of " <> name <> ", and GHC accepts its fits") $ do
                    Just typ <- typeOfExpression session ("undefined :: " <> signature)
                    found <- newIORef []
                    let options = defaultOptions{optionMaximumSize = size expected}
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
    parse = either error id . parseProgram
    size program = case program of
        Var _ -> 1
        App function argument -> size function + size argument
