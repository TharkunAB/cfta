{- | The edit trees of a term, as the terms of an automaton.

An edit tree is an edit set ("Data.CFTA.Edit.Sets") where an edit may lie inside
a wrap. An edit set has its edits at incomparable paths. So a change that wraps
a subterm and also changes something inside it costs a full replacement of the
subterm. In an edit tree the wrap puts a new node, or a new term with a hole,
above the old subterm, and the edits inside change the old subterm before it is
wrapped. 'editTreeAutomaton' gives an automaton whose terms are the edit trees.
'applyEditTree' gives the edited term of an edit tree.

__The term of an edit tree.__ The sites are the nodes of a chain in the preorder
of their positions, as for edit sets, and the size of a tree is the number of
edits plus the new material. The nesting is not in the term: it follows from the
preorder indexes. A site at the index @i@ with the end @e@ (the first index after
its subtree) is followed by a site with an index in @[e, N)@. A /treeable/ wrap
can also be followed by a site in @(i, e)@, which is inside the old subterm in
its hole, and by a wrap or an unwrap at the index @i@. The ranges are disjoint,
so the next site selects one: the cover of @[i + 1, N)@ and the sites at the
index @i@. So a tree has one run, and no split of a budget between a hole and the
later sites is needed: the number of the remaining edits is the same along the
chain.

__Which wraps can hold edits.__ The edits inside the hole are the sites of the
old subterm in the run of the whole term. In the new term the old subterm is at
the hole, in the state of the hole. The two runs agree when the hole has the state
of the position. So a wrap or a context wrap that holds edits needs that: it is
/treeable/. The other wraps are leaves, as in edit sets. (A hole in another state
needs the sites of the old subterm in that state: not built.) A context wrap has
a site for each kind: its new term has a hole of the state of the position, or a
hole of another state. The two kinds have different states for the new term, so
a context wrap has one run.

__Redundant forms.__ A replacement of the old subterm inside a wrap at the same
position gives the same term as one replacement at the position, and it costs one
more node (the wrap). So the tree does not allow a replacement after a wrap at its
index. A wrap after a wrap stays: it is not a replacement. An unwrap after a wrap
stays too: the wrap goes around a child of the old subterm, and no other edit with
this size does that.

__The edited term__ applies the edits from the last to the first: an edit inside
a wrap changes the old subterm before the wrap, and the order of the edits at
disjoint places does not matter.

The automaton must have no constraints, and the term must have exactly one run, as
for 'editAutomaton'.
-}
module Data.CFTA.Edit.Trees (
    TreeSymbol (..),
    TreeState (..),
    editTreeAutomaton,
    editsOfTree,
    applyEditTree,
) where

import Control.Monad (foldM)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Generics (Generic)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Edit
import Data.CFTA.Edit.Internal (bug, dyadicCover, extents, runStates, sitePath)
import Data.CFTA.Index (ChildIndex (..), TransitionIndex (..))
import Data.CFTA.Path (unPath)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A symbol of an edit tree.
data TreeSymbol symbol
    = -- | A site, with the rest of the chain as its last child.
      Link !(EditSymbol symbol)
    | -- | The last site of a tree: all its children are new material.
      Last !(EditSymbol symbol)
    | -- | A symbol of the new material.
      Inside !(EditSymbol symbol)
    deriving (Eq, Ord, Show, Generic)

instance (Hashable symbol) => Hashable (TreeSymbol symbol)

-- | A state of the automaton of edit trees.
data TreeState state symbol
    = -- | The initial state: the first site of a tree.
      TreeRoot
    | {- | The trees whose first site has a preorder index in the range (first
      index, number of indexes), with at most the given number of edits.
      -}
      TreeRange !(Int, Int) !Int
    | -- | The trees whose first site is a wrap or an unwrap at the index, with at most the given number of edits.
      TreeStackAt !Int !Int
    | -- | A state of the edit automaton below its root: the new material.
      TreeBelow !(EditState state symbol)
    deriving (Eq, Ord, Show)

type TreeTransition state symbol = FTA.Transition (TreeState state symbol) (TreeSymbol symbol) Constraint

-- | An edit site: its symbol, the preorder index of its position, the first index after its subtree, and the states of its new material.
data Site state symbol = Site
    { siteSymbol :: EditSymbol symbol
    , siteIndex :: !Int
    , siteEnd :: !Int
    , siteMaterial :: [TreeState state symbol]
    , siteStacks :: !Bool
    -- ^ A wrap, a context wrap, or an unwrap: it may follow a wrap at its index.
    , siteHolds :: !Bool
    -- ^ A treeable wrap or context wrap: the sites inside the old subterm may follow it.
    }

{- | The automaton of the edit trees of a term, of one to k edits. For k below 1
it has no term.
-}
editTreeAutomaton ::
    (Ord state, Ord symbol) =>
    Int ->
    FTA.PlainFTA state symbol ->
    Term symbol ->
    Either EditError (FTA.PlainFTA (TreeState state symbol) (TreeSymbol symbol))
editTreeAutomaton bound automaton given = do
    edits <- editAutomaton automaton given
    let allSites = sitesOf automaton edits given
        byIndex = Map.fromListWith (flip (<>)) [(siteIndex site, [site]) | site <- allSites]
        stacksAt = Map.fromListWith (flip (<>)) [(siteIndex site, [site]) | site <- allSites, siteStacks site]
        positions = length $ extents given
        total = until (>= positions) (* 2) 1
        -- The sites with an index in a range, in the order of the sites.
        inRange (start, size) = concat $ Map.elems $ Map.takeWhileAntitone (< start + size) $ Map.dropWhileAntitone (< start) byIndex
        -- Whether a range holds a site: the least index from its start on is inside it.
        holdsSite (start, size) = maybe False ((< start + size) . fst) $ Map.lookupGE start byIndex
        -- The ranges of the cover of the indexes from a bound on, without the ranges that hold no site.
        cover from = filter holdsSite $ dyadicCover total from
        -- The states of what may follow a site.
        followers remaining site
            | siteHolds site =
                [TreeRange range (remaining - 1) | range <- cover (siteIndex site + 1)]
                    <> [TreeStackAt (siteIndex site) (remaining - 1) | Map.member (siteIndex site) stacksAt]
            | otherwise = [TreeRange range (remaining - 1) | range <- cover (siteEnd site)]
        ends site = FTA.Transition (Last $ siteSymbol site) (siteMaterial site) noConstraint
        links remaining site =
            [ FTA.Transition (Link $ siteSymbol site) (siteMaterial site <> [next]) noConstraint
            | remaining > 1
            , next <- followers remaining site
            ]
        chosen remaining site = ends site : links remaining site
        rowOf TreeRoot = [transition | bound >= 1, site <- concat (Map.elems byIndex), transition <- chosen bound site]
        rowOf (TreeRange range remaining) = [transition | site <- inRange range, transition <- chosen remaining site]
        rowOf (TreeStackAt index remaining) = [transition | site <- Map.findWithDefault [] index stacksAt, transition <- chosen remaining site]
        rowOf (TreeBelow _) = []
        -- The hole sets that the sites use, which the edit automaton may not have.
        holeSets = Set.fromList [holeStates | site <- allSites, TreeBelow (Holed holeStates _) <- siteMaterial site]
        extra = concatMap (holedRows automaton) (Set.toList holeSets)
    pure $ close (materialRows edits <> materialRowsOf extra) rowOf

-- | The rows of the new material: the rows of the edit automaton without its root.
materialRows ::
    (Ord state, Ord symbol) =>
    FTA.PlainFTA (EditState state symbol) (EditSymbol symbol) ->
    [(TreeState state symbol, [TreeTransition state symbol])]
materialRows edits = materialRowsOf [row | row@(state, _) <- Map.toList $ FTA.transitionTable edits, state /= EditRoot]

-- | The rows of the new material from rows of the edit automaton.
materialRowsOf ::
    [(EditState state symbol, [FTA.Transition (EditState state symbol) (EditSymbol symbol) Constraint])] ->
    [(TreeState state symbol, [TreeTransition state symbol])]
materialRowsOf rows =
    [ ( TreeBelow state
      , [ FTA.Transition (Inside symbol) (map TreeBelow children) constraint
        | FTA.Transition symbol children constraint <- transitions
        ]
      )
    | (state, transitions) <- rows
    ]

-- | The automaton from the root, with the rows that the root reaches and the rows of the new material.
close ::
    (Ord state, Ord symbol) =>
    [(TreeState state symbol, [TreeTransition state symbol])] ->
    (TreeState state symbol -> [TreeTransition state symbol]) ->
    FTA.PlainFTA (TreeState state symbol) (TreeSymbol symbol)
close material rowOf =
    FTA.trim
        $ fromRight (bug "the automaton of edit trees of a ranked automaton is not ranked")
        $ FTA.mkFTA TreeRoot
        $ Map.toList
        $ Map.union (visit Map.empty [TreeRoot]) (Map.fromList material)
  where
    visit rows [] = rows
    visit rows (state : pending)
        | Map.member state rows = visit rows pending
        | otherwise =
            let row = rowOf state
             in visit
                    (Map.insert state row rows)
                    ([child | FTA.Transition _ children _ <- row, child <- children, isChain child] <> pending)
    isChain state = case state of
        TreeBelow _ -> False
        _ -> True

{- | The edit sites of the edit automaton, with the preorder extents of their
positions. A context wrap has a site for a hole of the state of its position,
which holds edits, and one for a hole of another state, which does not.
-}
sitesOf ::
    (Ord state, Ord symbol) =>
    FTA.PlainFTA state symbol ->
    FTA.PlainFTA (EditState state symbol) (EditSymbol symbol) ->
    Term symbol ->
    [Site state symbol]
sitesOf automaton edits given = concatMap sitesOfTransition $ FTA.transitionsFrom edits EditRoot
  where
    extentsOfPaths = Map.fromList $ extents given
    states = runStates automaton given
    unChild (ChildIndex index) = index
    sitesOfTransition (FTA.Transition symbol children _) =
        [ Site symbol index end (map TreeBelow children') (stacks symbol) holds
        | (children', holds) <- variants symbol children
        ]
      where
        (index, end) =
            Map.findWithDefault (bug "a site outside the term") (map unChild $ unPath $ sitePath symbol) extentsOfPaths
    stacks symbol = case symbol of
        WrapAt{} -> True
        ContextAt{} -> True
        UnwrapAt{} -> True
        _ -> False
    stateAt symbol = Map.lookup (map unChild $ unPath $ sitePath symbol) states
    -- The children of a site with whether the site holds edits.
    variants symbol children = case symbol of
        WrapAt _ _ (TransitionIndex index) (ChildIndex hole)
            | Just state <- stateAt symbol
            , (FTA.Transition _ siblings _) : _ <- drop index $ FTA.transitionsFrom automaton state
            , child : _ <- drop hole siblings ->
                [(children, child == state)]
        ContextAt{}
            | Just state <- stateAt symbol ->
                [ (map (replaceHole holeStates) children, holds)
                | (holds, holeStates) <- splitHole state children
                , not (Set.null holeStates)
                ]
        _ -> [(children, False)]
    -- The hole states of a context wrap that have the state of the position, and the others.
    splitHole state children = case [holeStates | Holed holeStates _ <- children] of
        holeStates : _ -> [(True, Set.intersection holeStates (Set.singleton state)), (False, Set.delete state holeStates)]
        [] -> []
    replaceHole holeStates child = case child of
        Holed _ other -> Holed holeStates other
        _ -> child

{- | The edits of an edit tree, in the order of the chain. 'Nothing' for a term
that is not an edit tree.
-}
editsOfTree :: Term (TreeSymbol symbol) -> Maybe [Edit symbol]
editsOfTree (Term.Node symbol children) = case symbol of
    Link site | not (null children) -> (:) <$> (Term.Node site <$> traverse material (init children)) <*> editsOfTree (last children)
    Last site -> (\new -> [Term.Node site new]) <$> traverse material children
    _ -> Nothing
  where
    material (Term.Node (Inside inner) grandchildren) = Term.Node inner <$> traverse material grandchildren
    material _ = Nothing

{- | The edited term of an edit tree: the edits from the last to the first.
'Nothing' when an edit does not fit the term, as for 'applyEdit'.
-}
applyEditTree :: Term symbol -> Term (TreeSymbol symbol) -> Maybe (Term symbol)
applyEditTree given tree = foldM applyEdit given . reverse =<< editsOfTree tree
