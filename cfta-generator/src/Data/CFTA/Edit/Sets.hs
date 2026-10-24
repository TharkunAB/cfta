{- | The edit sets of a term, as the terms of an automaton.

An edit set is the edits of a term at one to k sites at pairwise incomparable
paths ("Data.CFTA.Edit"). No path is a prefix of another, so no edit is inside
another, and the edits do not change the paths of each other. 'editSetAutomaton'
gives an automaton whose terms are the edit sets. 'applyEditSet' gives the edited
term of an edit set.

__The term of an edit set.__ The sites of a set are the nodes of a chain, in the
preorder of the paths. A site node has the symbol of its edit site, the new
material of the edit as its first children, and the rest of the chain as its
last child. The last site of a set has no chain child. So a set of j edits with
m nodes of new material has the size j + m. For one edit this is one more than
the new material, the size of the edit in 'editAutomaton', so for k = 1 the
automaton has the same size classes as the edit automaton. For a fixed total of
new material, a set with fewer edits comes first. An edit is a node of the edit
term, so it is not free.

__Why a chain.__ One root symbol for each set of sites has about C(sites, k)
root transitions: millions for k = 3 and a term of 100 nodes. A chain has one
node for each site, and it needs only the sites that may come next.

__Why not a plain chain.__ A site comes after the whole subtree of the site
before it, so the next site has a preorder index of at least @end@, the first
index after that subtree. A state for each @end@ allows exactly these sites. The
sites that come after a site are about n / 2, so the transitions are about
n^2 / 2 for k = 2, and the symbol of a site names the site, so no state can be
shared. A skip symbol would make the form linear, but a skip symbol adds size, and
the size would count positions and not edits.

__The dyadic cover.__ The indexes from @end@ on are covered by the dyadic ranges
of a segment tree over the preorder indexes: the canonical cover, at most
log N disjoint ranges. A site has one transition for each range of the cover of
its @end@, and the state of a range has the sites with an index in the range. The
ranges of a cover are disjoint, so the symbol of the next site, which names its
index, selects exactly one of them. So the choice is nondeterministic, but a set
has one run: the automaton is unambiguous when the edit automaton is. A site is
in at most log N ranges, so the number of transitions is
O(k * sites * log^2 n).

The automaton must have no constraints, and the term must have exactly one run, as
for 'editAutomaton'.
-}
module Data.CFTA.Edit.Sets (
    SetSymbol (..),
    SetState (..),
    editSetAutomaton,
    editsOfSet,
    applyEditSet,
) where

import Control.Monad (foldM)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import Data.List (mapAccumL)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Edit
import Data.CFTA.Index (ChildIndex (..))
import Data.CFTA.Path (Path, unPath)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A symbol of an edit set.
data SetSymbol symbol
    = -- | A site, with the rest of the chain as its last child.
      Link !(EditSymbol symbol)
    | -- | The last site of a set: all its children are new material.
      Last !(EditSymbol symbol)
    | -- | A symbol of the new material.
      Inside !(EditSymbol symbol)
    deriving (Eq, Ord, Show, Generic)

instance (Hashable symbol) => Hashable (SetSymbol symbol)

-- | A state of the automaton of edit sets.
data SetState state symbol
    = -- | The initial state: the first site of a set.
      SetRoot
    | {- | The sets whose first site has a preorder index in the range (first
      index, number of indexes), with at most the given number of edits.
      -}
      SetRange !(Int, Int) !Int
    | -- | A state of the edit automaton below its root: the new material.
      SetBelow !(EditState state symbol)
    deriving (Eq, Ord, Show)

type SetTransition state symbol = FTA.Transition (SetState state symbol) (SetSymbol symbol) Constraint

-- | An edit site: its symbol, the preorder index of its position, the first index after its subtree, and the states of its new material.
data Site state symbol = Site
    { siteSymbol :: EditSymbol symbol
    , siteIndex :: !Int
    , siteEnd :: !Int
    , siteMaterial :: [SetState state symbol]
    }

{- | The automaton of the edit sets of a term, of one to k edits. For k below 1
it has no term.
-}
editSetAutomaton ::
    (Ord state, Ord symbol) =>
    Int ->
    FTA.PlainFTA state symbol ->
    Term symbol ->
    Either EditError (FTA.PlainFTA (SetState state symbol) (SetSymbol symbol))
editSetAutomaton bound automaton given = do
    edits <- editAutomaton automaton given
    let byIndex = Map.fromListWith (flip (<>)) [(siteIndex site, [site]) | site <- sitesOf edits given]
        positions = length $ extents given
        total = until (>= positions) (* 2) 1
        -- The sites with an index in a range, in the order of the sites.
        inRange (start, size) = concat $ Map.elems $ Map.takeWhileAntitone (< start + size) $ Map.dropWhileAntitone (< start) byIndex
        -- Whether a range holds a site: the least index from its start on is inside it.
        holdsSite (start, size) = maybe False ((< start + size) . fst) $ Map.lookupGE start byIndex
        -- The ranges of the cover of the indexes from a bound on, without the ranges that hold no site.
        cover from = filter holdsSite $ dyadicCover total from
        ends site = FTA.Transition (Last $ siteSymbol site) (siteMaterial site) noConstraint
        links remaining site =
            [ FTA.Transition (Link $ siteSymbol site) (siteMaterial site <> [SetRange range (remaining - 1)]) noConstraint
            | remaining > 1
            , range <- cover (siteEnd site)
            ]
        chosen remaining site = ends site : links remaining site
        rowOf SetRoot = [transition | bound >= 1, site <- concat (Map.elems byIndex), transition <- chosen bound site]
        rowOf (SetRange range remaining) = [transition | site <- inRange range, transition <- chosen remaining site]
        rowOf (SetBelow _) = []
    pure $ close (materialRows edits) rowOf

-- | An impossible case.
bug :: String -> a
bug message = error $ "cfta-generator bug in Data.CFTA.Edit.Sets: " <> message

-- | The rows of the new material: the rows of the edit automaton without its root.
materialRows ::
    (Ord state, Ord symbol) =>
    FTA.PlainFTA (EditState state symbol) (EditSymbol symbol) ->
    [(SetState state symbol, [SetTransition state symbol])]
materialRows edits =
    [ ( SetBelow state
      , [ FTA.Transition (Inside symbol) (map SetBelow children) constraint
        | FTA.Transition symbol children constraint <- transitions
        ]
      )
    | (state, transitions) <- Map.toList $ FTA.transitionTable edits
    , state /= EditRoot
    ]

-- | The automaton from the root, with the rows that the root reaches and the rows of the new material.
close ::
    (Ord state, Ord symbol) =>
    [(SetState state symbol, [SetTransition state symbol])] ->
    (SetState state symbol -> [SetTransition state symbol]) ->
    FTA.PlainFTA (SetState state symbol) (SetSymbol symbol)
close material rowOf =
    FTA.trim
        $ fromRight (bug "the automaton of edit sets of a ranked automaton is not ranked")
        $ FTA.mkFTA SetRoot
        $ Map.toList
        $ Map.union (visit Map.empty [SetRoot]) (Map.fromList material)
  where
    visit rows [] = rows
    visit rows (state : pending)
        | Map.member state rows = visit rows pending
        | otherwise =
            let row = rowOf state
             in visit
                    (Map.insert state row rows)
                    ([child | FTA.Transition _ children _ <- row, child <- children, isRange child] <> pending)
    isRange state = case state of
        SetBelow _ -> False
        _ -> True

-- | The edit sites of the edit automaton, with the preorder extents of their positions.
sitesOf ::
    (Ord state, Ord symbol) =>
    FTA.PlainFTA (EditState state symbol) (EditSymbol symbol) ->
    Term symbol ->
    [Site state symbol]
sitesOf edits given =
    [ Site symbol index end (map SetBelow children)
    | FTA.Transition symbol children _ <- FTA.transitionsFrom edits EditRoot
    , let (index, end) =
            Map.findWithDefault
                (bug "a site outside the term")
                (map unChild $ unPath $ sitePath symbol)
                extentsOfPaths
    ]
  where
    extentsOfPaths = Map.fromList $ extents given
    unChild (ChildIndex index) = index

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

{- | The edits of an edit set, one for each site, in the order of the chain. The
paths are pairwise incomparable. 'Nothing' for a term that is not an edit set.
-}
editsOfSet :: Term (SetSymbol symbol) -> Maybe [Edit symbol]
editsOfSet (Term.Node symbol children) = case symbol of
    Link site | not (null children) -> (:) <$> (Term.Node site <$> traverse material (init children)) <*> editsOfSet (last children)
    Last site -> (\new -> [Term.Node site new]) <$> traverse material children
    _ -> Nothing
  where
    material (Term.Node (Inside inner) grandchildren) = Term.Node inner <$> traverse material grandchildren
    material _ = Nothing

{- | The edited term of an edit set. 'Nothing' when an edit does not fit the
term, as for 'applyEdit'. The edits are at incomparable paths, so their order
does not matter.
-}
applyEditSet :: Term symbol -> Term (SetSymbol symbol) -> Maybe (Term symbol)
applyEditSet given set = foldM applyEdit given =<< editsOfSet set
