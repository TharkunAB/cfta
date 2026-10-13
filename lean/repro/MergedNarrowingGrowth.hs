-- | Replay the historical recursive frontier using the old merge boundary branch.
module Main (main) where

import Control.Monad (unless)
import Data.CFTA.Interned
import Data.List (nub, transpose)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | The historical fixture uses one string alphabet.
type N = Node String

-- | The old merger exposes recursive boundary unions instead of retaining them.
legacyMerge :: N -> N
legacyMerge = go
  where
    go node@(Node edges) | null (freeVars node) = Node (concatMap group (Map.elems groups))
      where
        groups = Map.fromListWith (++) [((edgeSymbol edge, length (edgeChildren edge)), [edge]) | edge <- edges]
        group es@(edge : _) | length es > 4 = [Edge (edgeSymbol edge) (map mergedUnion (transpose (map edgeChildren es)))]
        group es = [setChildren edge (map go (edgeChildren edge)) | edge <- es]
    go node = node
    mergedUnion children = case nub kept of
        [single] -> single
        others
            | any recursiveBoundary others -> union others
            | otherwise -> go (union others)
      where
        recursive = [child | child@(InternedMu _) <- children, null (freeVars child)]
        kept =
            [ child
            | child <- children
            , child `elem` recursive || not (any (\big -> null (freeVars child) && legacySubsumes big child) recursive)
            ]

-- | Copy the source ancestor-pair comparison used by the old child filter.
legacySubsumes :: N -> N -> Bool
legacySubsumes = go Set.empty
  where
    go _ _ EmptyNode = True
    go _ EmptyNode _ = False
    go above b s
        | b == s = True
        | Set.member pair above = True
        | otherwise = all (\edge -> any (covers (Set.insert pair above) edge) (nodeEdges b)) (nodeEdges s)
      where
        pair = (nodeIdentity b, nodeIdentity s)
    covers above narrow wide =
        edgeSymbol wide == edgeSymbol narrow
            && length (edgeChildren wide) == length (edgeChildren narrow)
            && edgeConstraint wide == noConstraint
            && and (zipWith (go above) (edgeChildren wide) (edgeChildren narrow))

-- | The five distinct productive base labels.
names :: [String]
names = ["a", "b", "c", "d", "e"]

-- | A productive recursive unary language.
loop :: String -> N
loop name = Mu (\self -> Node [Edge name [], Edge "f" [self]])

-- | The empty recursive language retained by structural intersection.
dead :: N
dead = Mu (\self -> Node [Edge "f" [self]])

-- | Add the empty ordinary prefix observed after each old pass.
deadPrefix :: Int -> N
deadPrefix 0 = dead
deadPrefix rounds = Node [Edge "f" [deadPrefix (rounds - 1)]]

-- | One productive branch in the exact observed frontier recurrence.
branch :: Int -> String -> N
branch 0 name = loop name
branch rounds name = Node [Edge name [], Edge "f" [branch (rounds - 1) name], Edge "f" [deadPrefix (rounds - 1)]]

-- | Both equality peers have this same ordinary root after the given number of old passes.
frontier :: Int -> N
frontier rounds = Node ([Edge name [] | name <- names] ++ [Edge "f" [branch rounds name] | name <- names])

-- | Check source intersections against thirteen successive historical frontier equations.
main :: IO ()
main = do
    let matches rounds = intersect (legacyMerge (frontier rounds)) (frontier rounds) == frontier (rounds + 1)
        counts rounds = nodeCount (frontier rounds) == 6 * rounds + 6 && edgeCount (frontier rounds) == 16 * rounds + 20
    print [(rounds, matches rounds, nodeCount (frontier rounds), edgeCount (frontier rounds)) | rounds <- [0 .. 12]]
    unless (all (\rounds -> matches rounds && counts rounds) [0 .. 12]) (fail "historical recursive frontier differs")
