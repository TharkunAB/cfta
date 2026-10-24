{- | Shared parts of the edit sets and the edit trees: the positions of a term in
preorder, the path of an edit site, and the cover of a range of indexes by
dyadic ranges.
-}
module Data.CFTA.Edit.Internal (
    bug,
    extents,
    sitePath,
    dyadicCover,
    runStates,
) where

import Data.List (mapAccumL)
import qualified Data.Map.Strict as Map

import qualified Data.CFTA as FTA
import Data.CFTA.Edit (EditSymbol (..))
import Data.CFTA.Path (Path)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | An impossible case.
bug :: String -> a
bug message = error $ "cfta-generator bug in Data.CFTA.Edit: " <> message

-- | The preorder index and the first index after the subtree of each position of a term.
extents :: Term symbol -> [([Int], (Int, Int))]
extents = fst . go 0 []
  where
    go next at (Term.Node _ children) =
        let (after, inner) = mapAccumL step (next + 1) (zip [0 ..] children)
            step current (index, child) = let (found, following) = go current (at <> [index]) child in (following, found)
         in ((at, (next, after)) : concat inner, after)

-- | The path of an edit site.
sitePath :: EditSymbol symbol -> Path
sitePath symbol = case symbol of
    ReplaceAt at -> at
    WrapAt at _ _ _ -> at
    UnwrapAt at _ -> at
    ContextAt at _ _ _ -> at
    HoleParent _ _ -> mempty
    Material _ -> mempty

{- | The canonical cover of the indexes from a bound up to a power of two by
dyadic ranges (first index, number of indexes): the largest aligned range that
starts at the bound and fits, and then the cover of the rest.
-}
dyadicCover :: Int -> Int -> [(Int, Int)]
dyadicCover total = go
  where
    go from
        | from >= total = []
        | otherwise = let size = largest from in (from, size) : go (from + size)
    largest from = last [size | size <- takeWhile (<= total) (iterate (* 2) 1), from `mod` size == 0, from + size <= total]

-- | The state of the run of the automaton on each position of a term. The term has one run.
runStates :: (Ord state, Eq symbol) => FTA.PlainFTA state symbol -> Term symbol -> Map.Map [Int] state
runStates automaton given = case go (FTA.initialState automaton) given of
    run : _ -> run
    [] -> Map.empty
  where
    go state (Term.Node symbol children) =
        [ Map.insert [] state $ Map.unions [Map.mapKeys (index :) childRun | (index, childRun) <- zip [0 ..] childRuns]
        | FTA.Transition other childStates _ <- FTA.transitionsFrom automaton state
        , other == symbol
        , length childStates == length children
        , childRuns <- sequence $ zipWith go childStates children
        ]
