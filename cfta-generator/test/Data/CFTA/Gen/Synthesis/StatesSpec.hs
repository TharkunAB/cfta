{-# LANGUAGE OverloadedStrings #-}

{- | An end-to-end test of "Data.CFTA.Gen.Synthesis.States" with a host in
memory: a goal is a type name, a leaf's step passes when its result is the
goal, and the checker kills each program that has one of some leaves.
-}
module Data.CFTA.Gen.Synthesis.StatesSpec (spec) where

import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldReturn)

import Data.CFTA.Gen.Synthesis (renderProgram)
import Data.CFTA.Gen.Synthesis.States (Goals (..), Refinement (..), searchStates)
import Data.CFTA.Gen.Synthesis.Walk

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis.States" $ do
    it "gives the programs of the goals size by size, in the host's order" $
        fitsWithout [] `shouldReturn` (["length xs", "sum xs", "length (reverse xs)", "sum (reverse xs)"], Exhausted)
    it "leaves out the programs under a prefix that the checker kills" $
        fitsWithout ["reverse"] `shouldReturn` (["length xs", "sum xs"], Exhausted)

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

-- | The fits of programs up to size 3, and the outcome, with a checker that kills the leaves of the list.
fitsWithout :: [Text] -> IO ([String], Outcome)
fitsWithout dead = do
    held <- newIORef 0
    found <- newIORef []
    let extend tokens = do
            kept <- readIORef held
            case [index | (index, (name, _)) <- zip [0 ..] tokens, name `elem` dead] of
                index : _ -> Died (kept + index) <$ writeIORef held (kept + index)
                [] -> Done True <$ writeIORef held (kept + length tokens)
        hooks = Hooks (\_ _ -> pure ()) (\_ _ -> pure ()) (\_ -> pure True)
    (progress, _) <- searchStates (Limits 3 Nothing Nothing) (Checker (writeIORef held) extend) hooks goals [] $ \fit ->
        True <$ modifyIORef' found (renderProgram (fitProgram fit) :)
    fits <- reverse <$> readIORef found
    pure (fits, progressOutcome progress)
