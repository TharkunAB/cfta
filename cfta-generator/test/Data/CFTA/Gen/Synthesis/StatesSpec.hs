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
import Data.CFTA.Gen.Synthesis.States (
    EdgeOrder (..),
    Figures (..),
    Goals (..),
    Refinement (..),
    Walking (..),
    searchStatesWith,
 )
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
    it "lists the programs that Hectare's rule leaves next to an emptied child" $ do
        -- length xs goes, so the child of length under inc at size 3 has no
        -- program, and length (reverse xs) at the root stays.
        let rule = [(["length"], Just ["xs"])]
            fits walking =
                (\(found, progress, figures) -> (found, progressSkipped progress, figuresCount figures))
                    <$> searchWith withInc walking 3 rule (const [])
        fits (Enumerated HostOrder)
            `shouldReturn` (["sum xs", "length (reverse xs)", "sum (reverse xs)", "inc (sum xs)"], 0, 4)
        (\(found, _, _) -> found) <$> fits Preorder
            `shouldReturn` ["sum xs", "length (reverse xs)", "sum (reverse xs)", "inc (sum xs)"]
    it "leaves Hectare's rule for the first argument out of the automaton, as the depth-first search does" $ do
        search Preorder 3 [(["length"], Just ["xs"])] []
            `shouldReturn` (["sum xs", "length (reverse xs)", "sum (reverse xs)"], 0, 0)
        search (Enumerated HostOrder) 3 [(["length"], Just ["xs"])] []
            `shouldReturn` (["sum xs", "length (reverse xs)", "sum (reverse xs)"], 0, 3)
  where
    programs = ["length xs", "sum xs", "length (reverse xs)", "sum (reverse xs)"]

-- | The leaves: a name, the types of the children, and the result type.
leaves :: [(Text, [Text], Text)]
leaves = [("xs", [], "List"), ("length", ["List"], "Int"), ("sum", ["List"], "Int"), ("reverse", ["List"], "List")]

-- | The goals of a query of type @Int@ that must use @xs@, over 'leaves'.
goals :: Goals IO Text
goals = goalsOf leaves

-- | 'goals', with a leaf @inc@ from @Int@ to @Int@.
withInc :: Goals IO Text
withInc = goalsOf (leaves <> [("inc", ["Int"], "Int")])

-- | The goals of a query of type @Int@ that must use @xs@; the rank is the leaf's index.
goalsOf :: [(Text, [Text], Text)] -> Goals IO Text
goalsOf leaves' = Goals [name | (name, _, _) <- leaves'] [0] "Int" $ \_ goal counts ->
    pure
        ( Just
            [ Refinement index index (length children) children
            | (index, (_, children, result)) <- zip [0 ..] leaves'
            , result == goal
            , length children `elem` counts
            ]
        )

-- | The fits of programs up to size 3, and the outcome, with a walking and a checker that kills the leaves of the list.
fitsWithout :: Walking -> [Text] -> IO ([String], Outcome)
fitsWithout walking dead = do
    (fits, progress, _) <- searchFigures walking 3 [] dead
    pure (fits, progressOutcome progress)

{- | The fits up to a size, the programs skipped under a dead prefix, and the
programs that the automata count, with Hectare's rules and a checker that
kills the leaves of the list.
-}
search :: Walking -> Int -> [([Text], Maybe [Text])] -> [Text] -> IO ([String], Int, Integer)
search walking size avoid dead = do
    (fits, progress, figures) <- searchFigures walking size avoid dead
    pure (fits, progressSkipped progress, figuresCount figures)

-- | 'search', with all the figures.
searchFigures :: Walking -> Int -> [([Text], Maybe [Text])] -> [Text] -> IO ([String], Progress, Figures)
searchFigures walking size avoid dead = searchWith goals walking size avoid (\names -> [index | (index, name) <- zip [0 ..] names, name `elem` dead])

{- | The fits up to a size, the progress, and the figures, with Hectare's
rules and a checker that kills a program at the first of the indices that
the function gives for the names of its leaves in preorder.
-}
searchWith ::
    Goals IO Text -> Walking -> Int -> [([Text], Maybe [Text])] -> ([Text] -> [Int]) -> IO ([String], Progress, Figures)
searchWith goals' walking size avoid kills = do
    -- The names of the leaves of the checked prefix.
    held <- newIORef []
    found <- newIORef []
    let extend tokens = do
            names <- (<> map fst tokens) <$> readIORef held
            case kills names of
                index : _ -> Died index <$ writeIORef held (take index names)
                [] -> Done True <$ writeIORef held names
        truncate' count = modifyIORef' held (take count)
        hooks = Hooks (\_ _ -> pure ()) (\_ _ -> pure ()) (\_ -> pure True)
    (progress, figures) <- searchStatesWith walking (Limits size Nothing Nothing) (Checker truncate' extend) hooks goals' avoid $ \fit ->
        True <$ modifyIORef' found (renderProgram (fitProgram fit) :)
    fits <- reverse <$> readIORef found
    pure (fits, progress, figures)
