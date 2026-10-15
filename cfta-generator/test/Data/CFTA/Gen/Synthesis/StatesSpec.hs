{-# LANGUAGE OverloadedStrings #-}

{- | An end-to-end test of "Data.CFTA.Gen.Synthesis.States" with a host in
memory: a goal is a type name, a leaf's step passes when its result is the
goal, and the checker kills each program that has one of some leaves.
-}
module Data.CFTA.Gen.Synthesis.StatesSpec (spec) where

import Data.Bifunctor (first)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (sort)
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldReturn)

import Data.CFTA.Gen.Synthesis (renderProgram)
import Data.CFTA.Gen.Synthesis.States (EdgeOrder (..), Goals (..), Refinement (..), Walking (..), searchStatesWith)
import Data.CFTA.Gen.Synthesis.Walk

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis.States" $ do
    it "gives the programs of the goals size by size, in the host's order" $
        fitsWithout Preorder [] `shouldReturn` (programs, Exhausted)
    it "leaves out the programs under a prefix that the checker kills" $
        fitsWithout Preorder ["reverse"] `shouldReturn` (["length xs", "sum xs"], Exhausted)
    it "gives the same programs through the automaton of each size, in the host's order" $ do
        fitsWithout (Enumerated HostOrder) [] `shouldReturn` (programs, Exhausted)
        fitsWithout (Enumerated HostOrder) ["reverse"] `shouldReturn` (["length xs", "sum xs"], Exhausted)
    it "gives the same programs through the automaton in the enumerator's order" $
        first sort <$> fitsWithout (Enumerated CanonicalOrder) []
            `shouldReturn` (sort programs, Exhausted)
  where
    programs = ["length xs", "sum xs", "length (reverse xs)", "sum (reverse xs)"]

-- | The leaves: a name, the types of the children, and the result type.
leaves :: [(Text, [Text], Text)]
leaves = [("xs", [], "List"), ("length", ["List"], "Int"), ("sum", ["List"], "Int"), ("reverse", ["List"], "List")]

-- | The goals of a query of type @Int@ that must use @xs@; the rank is the leaf's index.
goals :: Goals IO Text
goals = Goals [name | (name, _, _) <- leaves] [0] "Int" $ \_ goal counts ->
    pure
        ( Just
            [ Refinement index index (length children) children
            | (index, (_, children, result)) <- zip [0 ..] leaves
            , result == goal
            , length children `elem` counts
            ]
        )

-- | The fits of programs up to size 3, and the outcome, with a walking and a checker that kills the leaves of the list.
fitsWithout :: Walking -> [Text] -> IO ([String], Outcome)
fitsWithout walking dead = do
    held <- newIORef 0
    found <- newIORef []
    let extend tokens = do
            kept <- readIORef held
            case [index | (index, (name, _)) <- zip [0 ..] tokens, name `elem` dead] of
                index : _ -> Died (kept + index) <$ writeIORef held (kept + index)
                [] -> Done True <$ writeIORef held (kept + length tokens)
        hooks = Hooks (\_ _ -> pure ()) (\_ _ -> pure ()) (\_ -> pure True)
    (progress, _) <- searchStatesWith walking (Limits 3 Nothing Nothing) (Checker (writeIORef held) extend) hooks goals [] $ \fit ->
        True <$ modifyIORef' found (renderProgram (fitProgram fit) :)
    fits <- reverse <$> readIORef found
    pure (fits, progressOutcome progress)
