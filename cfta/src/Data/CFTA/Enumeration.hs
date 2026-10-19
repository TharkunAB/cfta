{-# LANGUAGE OverloadedStrings #-}

{- | Enumeration of constrained automata.

One enumerator serves every constraint theory. It builds 'TermFragment's
before expanding them to concrete @Term@s. The path equalities of a
constraint ('equalities') are suspended obligations that point at UVars:
when enumeration descends through an edge, those obligations descend with
it, and when one reaches the node it names, the UVars are merged so future
choices stay consistent. A constraint with a 'residual' beyond its
equalities is recorded with the subterm it guards, and 'runs' hands those
pairs to the caller to decide. 'terms' lists an automaton with no
constraint and no recursive binder level by level, without the enumeration
state. A cyclic one always uses the enumeration state, and enumeration stops
at a recursive binder. Only 'plainTerms' lists a cyclic graph without
constraints, as an infinite lazy list.

Most callers use 'terms' or 'runs'. The lower-level state operations are
exposed for pruning oracles and downstream tools that need to inspect or
steer enumeration.
-}
module Data.CFTA.Enumeration (
    -- * Terms and runs
    terms,
    termsWith,
    runs,
    runsBy,
    runsNarrowedBy,
    runsInterned,
    truncatedTerms,
    plainTerms,
    plainTermsAtMost,
    unconstrained,
    reachesConstrainedMu,
    provablyEmpty,

    -- * Pruning oracles
    termsPrune,
    termsPruneWith,
    OrderedConfig (..),
    OrderedCursor,
    OrderedNext (..),
    OrderedPauseReason (..),
    OrderedStatistics,
    startOrdered,
    strengthenOrdered,
    nextOrdered,
    orderedStatistics,
    getUnexpandedNode,
    ExpansionOrder,
    noExpansionPreference,
    expandPartialTermFrag,
    getUVarRepresentative,

    -- * Fragments
    TermFragment (..),
    PartialSymbol (..),
    EnumerateM,
) where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus, forM_, guard, mzero, unless, when, zipWithM)
import Control.Monad.State.Strict (MonadState, gets, modify')
import qualified Control.Monad.State.Strict as State
import qualified Data.Foldable as Foldable
import Data.Hashable (Hashable (..))
import qualified Data.IntSet as IntSet
import Data.List (compareLength, genericTake, sortOn, transpose)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (All (..))
import Data.Ord (Down (..))
import Data.Sequence (Seq ((:<|)))
import qualified Data.Sequence as Sequence
import qualified Data.Set as Set
import Data.String (IsString (..))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, typeRep)

import Data.CFTA.Equality.Constraint (
    EqConstraints (EmptyConstraints, EqContradiction),
    PathEClass (getPathTrie),
    PathTrie (PathTrie),
    combineEqConstraints,
    isTerminalPathTrie,
    unPathEClass,
    unsafeGetEclasses,
 )
import Data.CFTA.Index (Depth (..))
import qualified Data.CFTA.Internal.OrderedFrontier as Frontier
import Data.CFTA.Internal.Tree (termLevelsBy)
import Data.CFTA.Internal.UnionFind (UVar, UVarGen, UnionFind, intToUVar, uvarToInt)
import qualified Data.CFTA.Internal.UnionFind as UnionFind
import Data.CFTA.Interned
import Data.CFTA.Interned.Memo (TypeableMemoCache, memoTypeableWith, newTypeableMemoCache)
import Data.CFTA.Path (Pathable (getPath))
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import qualified Data.HashSet as HashSet
import qualified Data.IntMap.Strict as IntMap

-------------------------------------------------------------------------------

---------------------------------------------------------------------------
------------------------------- Term fragments ----------------------------
---------------------------------------------------------------------------

-- | Partially enumerated term with holes for nodes that still need expansion.
data TermFragment symbol
    = -- | Concrete symbol with already-created child fragments.
      TermFragmentNode !symbol ![TermFragment symbol]
    | -- | Hole whose value is tracked in the enumeration state.
      TermFragmentUVar UVar
    deriving (Eq, Ord, Show)

{- | A label in a term that may still contain enumeration holes.

Keeping holes outside the caller's alphabet prevents a real symbol from being
mistaken for a rendered placeholder such as @v0@. 'TruncatedRecursion' records a
recursive node that enumeration has finished with: one carrying no suspended
constraints, which is where enumeration stops. A recursive node that still has
constraints pending is a 'UVarHole', because it may still be expanded.
-}
data PartialSymbol symbol
    = -- | A symbol from the automaton's alphabet.
      ConcreteSymbol !symbol
    | -- | An unexpanded enumeration variable.
      UVarHole !UVar
    | -- | Enumeration stopped at an unconstrained recursive node.
      TruncatedRecursion
    deriving (Eq, Ord, Show)

instance (Hashable symbol) => Hashable (PartialSymbol symbol) where
    hashWithSalt salt (ConcreteSymbol symbol) =
        salt `hashWithSalt` (0 :: Int) `hashWithSalt` symbol
    hashWithSalt salt (UVarHole uv) =
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` (uvarToInt uv)
    hashWithSalt salt TruncatedRecursion =
        salt `hashWithSalt` (2 :: Int)

---------------------------------------------------------------------------
------------------------------ Enumeration state --------------------------
---------------------------------------------------------------------------

-----------------------
------- Suspended constraints
-----------------------

-- | Equality obligation that has not yet reached the node it constrains.
data SuspendedConstraint = SuspendedConstraint !PathTrie !UVar
    deriving (Eq, Show)

-- | Remaining paths for a suspended equality obligation.
scGetPathTrie :: SuspendedConstraint -> PathTrie
scGetPathTrie (SuspendedConstraint pt _) = pt

-- | UVar that must be merged when the suspended obligation is reached.
scGetUVar :: SuspendedConstraint -> UVar
scGetUVar (SuspendedConstraint _ uv) = uv

{- | Push suspended obligations into the children they reach, by child index.

Each child gets its obligations in the order of the input. An obligation that
reaches no child, because its paths end here, goes to no child.
-}
descendScs ::
    (Foldable f) =>
    IntMap.IntMap (Seq SuspendedConstraint) -> f SuspendedConstraint -> IntMap.IntMap (Seq SuspendedConstraint)
descendScs = Foldable.foldl' descend
  where
    descend children (SuspendedConstraint (PathTrie tries) uv) =
        IntMap.foldlWithKey'
            (\m i pt -> IntMap.insertWith (flip (<>)) i (Sequence.singleton (SuspendedConstraint pt uv)) m)
            children
            tries
    descend children _ = children

-----------------------
------- UVarValue
-----------------------

-- | Enumeration status for one UVar.
data UVarValue symbol
    = -- | UVar still has a node to expand.
      UVarUnenumerated
        -- | Node still to enumerate, or 'Nothing' for pure constraint variables.
        !(Maybe (Node symbol))
        -- | Constraints that should be carried while enumerating this value.
        !(Seq SuspendedConstraint)
    | -- | UVar has been expanded to a fragment.
      UVarEnumerated !(TermFragment symbol)
    | -- | UVar was merged into another representative and should no longer be used.
      UVarEliminated
    deriving (Eq, Show)

{- | Intersect two UVar values. With the first argument true, an intersection
that provably accepts no term becomes 'EmptyNode' (see '_constrainedRecursion').
-}
intersectUVarValue ::
    (Hashable symbol, Typeable symbol) =>
    Bool -> UVarValue symbol -> UVarValue symbol -> UVarValue symbol
intersectUVarValue checkEmpty (UVarUnenumerated mn1 scs1) (UVarUnenumerated mn2 scs2) =
    let newContents = case (mn1, mn2) of
            (Nothing, x) -> x
            (x, Nothing) -> x
            (Just n1, Just n2) -> Just (emptyIfProvably (n1 `intersect` n2))
        newConstraints = scs1 <> scs2
     in UVarUnenumerated newContents newConstraints
  where
    -- An intersection can unfold a recursive node with constraints into a
    -- node that needs itself again with no base case. Enumeration of such a
    -- node would not end, so the merge makes it 'EmptyNode', and the caller
    -- ends the branch.
    emptyIfProvably n
        | checkEmpty, reachesConstrainedMu n, provablyEmpty n = EmptyNode
        | otherwise = n
intersectUVarValue _ UVarEliminated _ = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ _ UVarEliminated = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ _ _ = error "intersectUVarValue: Intersecting with enumerated value not implemented"

-----------------------
------- Top-level state
-----------------------

-- | Mutable state threaded through nondeterministic enumeration branches.
data EnumerationState symbol = EnumerationState
    { _uvarCounter :: !UVarGen
    -- ^ Fresh UVar supply.
    , _uvarRepresentative :: !UnionFind
    -- ^ Persistent union-find for equality-constrained UVars.
    , _uvarValues :: !(IntMap.IntMap (UVarValue symbol))
    {- ^ Per-UVar contents keyed by 'uvarToInt'. A slot is
    'UVarEliminated' exactly when its UVar is not a representative;
    @findExpandableUVars@ relies on 'assimilateUvarVal' maintaining this.
    -}
    , _expandableUVars :: !IntSet.IntSet
    {- ^ The slots of '_uvarValues' that 'expandable' accepts. Every write of
    a slot updates this set.
    -}
    , _waitingUVars :: !(IntMap.IntMap Int)
    {- ^ For each representative UVar, how many suspended constraints of
    'UVarUnenumerated' slots name a UVar of its class. A class with no such
    constraint has no entry. Every write of a slot updates this map, and a
    union moves the count of the old representatives to the new one.
    -}
    , _obligations :: [(Constraint, TermFragment symbol)]
    -- ^ Constraints with a 'residual', each with the fragment it guards.
    , _recursionAncestry :: !(IntMap.IntMap RecursionAncestry)
    {- ^ For each UVar that the expansion of a constrained recursive node
    reached, directly or through later expansions, the keys of those
    expansions.
    -}
    , _expansionAncestry :: !RecursionAncestry
    -- ^ The ancestry that the current expansion gives the UVars it reaches.
    , _edgesOf :: Node symbol -> [Edge symbol]
    {- ^ The edges of a node in the order of enumeration. It is one function,
    set once for the enumeration, so a step that copies the state copies one
    field for it.
    -}
    , _constrainedRecursion :: !Bool
    {- ^ Whether the root reaches a recursive node with constraints. Only then
    can a merge unfold one, so only then does a merge run 'provablyEmpty'.
    -}
    }

{- | The expansions of constrained recursive nodes that a UVar descends from,
each as its 'recursionKey'.
-}
type RecursionAncestry = HashSet.HashSet RecursionKey

{- | A recursive node with the paths suspended on it. Two expansions with one
key differ only in their UVars.
-}
data RecursionKey = RecursionKey
    { recursiveNode :: !NodeId
    , suspendedTries :: !(HashSet.HashSet PathTrie)
    }
    deriving (Eq, Show)

-- | Hash the two fields in order, as the hash of a pair does.
instance Hashable RecursionKey where
    hashWithSalt salt (RecursionKey node tries) = salt `hashWithSalt` node `hashWithSalt` tries

-- | The key of a recursive node with its suspended constraints.
recursionKey :: Node symbol -> Seq SuspendedConstraint -> RecursionKey
recursionKey n scs =
    RecursionKey
        { recursiveNode = nodeIdentity n
        , suspendedTries = HashSet.fromList $ map scGetPathTrie $ Foldable.toList scs
        }

{- | Initial state whose root UVar contains the node being enumerated, with
the order of the edges of each node.
-}
initEnumerationState :: (Typeable symbol) => (Node symbol -> [Edge symbol]) -> Node symbol -> EnumerationState symbol
initEnumerationState edgesOf n =
    let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
        value = UVarUnenumerated (Just n) Sequence.Empty
     in EnumerationState
            uvg
            (UnionFind.withInitialValues [uv])
            (IntMap.singleton (uvarToInt uv) value)
            (if expandable value then IntSet.singleton (uvarToInt uv) else IntSet.empty)
            IntMap.empty
            []
            IntMap.empty
            HashSet.empty
            edgesOf
            (reachesConstrainedMu n)

---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------

{- | Nondeterministic enumeration with one state for each branch.

A computation gets the state, a success continuation, and the result of the
branches after it. The success continuation gets a result, the new state, and
the result of the branches after it. The branches run depth first, in the
order of @StateT state []@, but a bind builds no intermediate list.
-}
newtype EnumerateM symbol a = EnumerateM
    { runEnumerateM ::
        forall r.
        EnumerationState symbol ->
        (a -> EnumerationState symbol -> r -> r) ->
        r ->
        r
    }

instance Functor (EnumerateM symbol) where
    {-# INLINE fmap #-}
    fmap f (EnumerateM m) = EnumerateM $ \s success later -> m s (success . f) later

instance Applicative (EnumerateM symbol) where
    {-# INLINE pure #-}
    pure a = EnumerateM $ \s success later -> success a s later
    {-# INLINE (<*>) #-}
    EnumerateM mf <*> EnumerateM ma =
        EnumerateM $ \s success later -> mf s (\f s' later' -> ma s' (success . f) later') later

instance Monad (EnumerateM symbol) where
    {-# INLINE (>>=) #-}
    EnumerateM m >>= k =
        EnumerateM $ \s success later -> m s (\a s' later' -> runEnumerateM (k a) s' success later') later

instance Alternative (EnumerateM symbol) where
    {-# INLINE empty #-}
    empty = EnumerateM $ \_ _ later -> later
    {-# INLINE (<|>) #-}
    EnumerateM m <|> EnumerateM n = EnumerateM $ \s success later -> m s success (n s success later)

instance MonadPlus (EnumerateM symbol)

-- | A failed pattern match ends the branch.
instance MonadFail (EnumerateM symbol) where
    {-# INLINE fail #-}
    fail _ = empty

-- | Like @StateT@ from "Control.Monad.State.Strict", 'state' forces the pair that its function gives.
instance MonadState (EnumerationState symbol) (EnumerateM symbol) where
    {-# INLINE state #-}
    state f = EnumerateM $ \s success later -> case f s of (a, s') -> success a s' later

-- | One branch for each element, in order.
branches :: [a] -> EnumerateM symbol a
{-# INLINE branches #-}
branches xs = EnumerateM $ \s success later -> foldr (\x rest -> success x s rest) later xs

-- | The result and the final state of every branch, in order, lazily.
allBranches :: EnumerateM symbol a -> EnumerationState symbol -> [(a, EnumerationState symbol)]
allBranches (EnumerateM m) s = m s (\a s' rest -> (a, s') : rest) []

---------------------
-------- UVar accessors
---------------------

nextUVar :: EnumerateM symbol UVar
nextUVar = do
    c <- gets _uvarCounter
    let (c', uv) = UnionFind.nextUVar c
    modify' $ \s -> s{_uvarCounter = c'}
    return uv

addUVarValue :: Maybe (Node symbol) -> EnumerateM symbol UVar
addUVarValue x = do
    uv <- nextUVar
    let value = UVarUnenumerated x Sequence.Empty
    modify' $ \s ->
        s
            { _uvarValues = IntMap.insert (uvarToInt uv) value (_uvarValues s)
            , _expandableUVars =
                if expandable value
                    then IntSet.insert (uvarToInt uv) (_expandableUVars s)
                    else _expandableUVars s
            }
    inheritAncestry (uvarToInt uv)
    return uv

-- | Give one UVar the ancestry of the current expansion.
inheritAncestry :: Int -> EnumerateM symbol ()
inheritAncestry idx = do
    current <- gets _expansionAncestry
    unless (HashSet.null current) $
        modify' $
            \s -> s{_recursionAncestry = IntMap.insertWith HashSet.union idx current (_recursionAncestry s)}

-- | Return the current representative for a UVar, updating union-find state.
getUVarRepresentative :: UVar -> EnumerateM symbol UVar
getUVarRepresentative uv = do
    uf <- gets _uvarRepresentative
    let (uv', uf') = UnionFind.find uv uf
    modify' $ \s -> s{_uvarRepresentative = uf'}
    return uv'

-- | Look up the value for a UVar after path-compressing its representative.
getUVarValue :: UVar -> EnumerateM symbol (UVarValue symbol)
getUVarValue uv = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    values <- gets _uvarValues
    return $ values IntMap.! idx

{- | Replace the value of a UVar.

Unlike 'getUVarValue', this writes the UVar itself, not its representative.
'assimilateUvarVal' needs this to eliminate a UVar that was a representative
before a union.
-}
setUVarValue :: UVar -> UVarValue symbol -> EnumerateM symbol ()
setUVarValue uv val = do
    old <- gets (\s -> _uvarValues s IntMap.! uvarToInt uv)
    writeUVarValue (suspended val) (suspended old) uv val
  where
    suspended (UVarUnenumerated _ scs) = scs
    suspended _ = Sequence.Empty

{- | 'setUVarValue' with the suspended constraints that the slot gains and
loses, for a caller that knows them: the constraints that stay in the slot
change no count.
-}
writeUVarValue ::
    Seq SuspendedConstraint -> Seq SuspendedConstraint -> UVar -> UVarValue symbol -> EnumerateM symbol ()
writeUVarValue gained lost uv val =
    modify' $ \s ->
        s
            { _uvarValues = IntMap.insert idx val (_uvarValues s)
            , _expandableUVars =
                if expandable val
                    then IntSet.insert idx (_expandableUVars s)
                    else IntSet.delete idx (_expandableUVars s)
            , _waitingUVars = count (_uvarRepresentative s) 1 gained (count (_uvarRepresentative s) (-1) lost (_waitingUVars s))
            }
  where
    idx = uvarToInt uv
    count uf change scs waiting =
        Foldable.foldl' (\m sc -> IntMap.alter (add change) (uvarToInt (UnionFind.root (scGetUVar sc) uf)) m) waiting scs
    add change old = case maybe change (+ change) old of
        0 -> Nothing
        new -> Just new

{- | Whether a slot holds a node that enumeration can expand. An
unconstrained recursive node is the base case of a recursion: expanding it
would unfold forever with nothing to stop it.
-}
expandable :: UVarValue symbol -> Bool
expandable (UVarUnenumerated (Just node) scs) = not (recursiveBoundary node && Sequence.null scs)
expandable _ = False

---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM symbol SuspendedConstraint
pecToSuspendedConstraint pec = do
    uv <- addUVarValue Nothing
    return $ SuspendedConstraint (getPathTrie pec) uv

---------------------
-------- Merging UVar's / nodes
---------------------

-- | Merge the source UVar into the target UVar, intersecting their constraints.
assimilateUvarVal ::
    (Hashable symbol, Typeable symbol) => UVar -> UVar -> EnumerateM symbol ()
assimilateUvarVal uvTarg uvSrc
    | uvTarg == uvSrc = return ()
    | otherwise = do
        values <- gets _uvarValues
        let srcVal = values IntMap.! uvarToInt uvSrc
        let targVal = values IntMap.! uvarToInt uvTarg
        case srcVal of
            UVarEliminated -> return () -- Happens from duplicate constraints
            _ -> do
                checkEmpty <- gets _constrainedRecursion
                let v = intersectUVarValue checkEmpty srcVal targVal
                guard $ not $ hasEmptyContents v
                -- The suspended constraints of the source move to the
                -- target, in the same class, so no count changes.
                writeUVarValue Sequence.Empty Sequence.Empty uvTarg v
                writeUVarValue Sequence.Empty Sequence.Empty uvSrc UVarEliminated
                modify' $ \s -> case IntMap.lookup (uvarToInt uvSrc) (_recursionAncestry s) of
                    Nothing -> s
                    Just ancestry -> s{_recursionAncestry = IntMap.insertWith HashSet.union (uvarToInt uvTarg) ancestry (_recursionAncestry s)}

-- | Intersect a node and inherited constraints into the value for a UVar.
mergeNodeIntoUVarVal ::
    (Hashable symbol, Typeable symbol) =>
    UVar -> Node symbol -> Seq SuspendedConstraint -> EnumerateM symbol ()
mergeNodeIntoUVarVal uv n scs = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    values <- gets _uvarValues
    checkEmpty <- gets _constrainedRecursion
    let new = intersectUVarValue checkEmpty (UVarUnenumerated (Just n) scs) (values IntMap.! idx)
    -- The slot keeps its suspended constraints and gains these.
    writeUVarValue scs Sequence.Empty uv' new
    inheritAncestry idx
    guard $ not $ hasEmptyContents new

-- | Whether an unenumerated variable has already reduced to the empty node.
hasEmptyContents :: UVarValue symbol -> Bool
hasEmptyContents (UVarUnenumerated (Just EmptyNode) _) = True
hasEmptyContents _ = False

---------------------
-------- Core enumeration algorithm
---------------------

-- | Table for 'unconstrained'.
unconstrainedCache :: TypeableMemoCache
unconstrainedCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE unconstrainedCache #-}

{- | Whether no edge reachable from the node carries a constraint: no path
equality and no residual. Such an automaton is an ordinary tree automaton,
recursive or not.
-}
unconstrained :: forall symbol. (Typeable symbol) => Node symbol -> Bool
unconstrained = memoTypeableWith @symbol unconstrainedCache $ getAll . crush free
  where
    free (Node es) = All (all (\e -> equalities (edgeConstraint e) == EmptyConstraints && not (residual (edgeConstraint e))) es)
    free _ = All True

{- | Whether a closed node reaches a recursive node with constraints. A
recursive node without constraints reaches no constraint at all, so the walk
does not enter it.
-}
reachesConstrainedMu :: forall symbol. (Typeable symbol) => Node symbol -> Bool
reachesConstrainedMu = memoTypeableWith @symbol reachesConstrainedMuCache go
  where
    go n | numNestedMu n == 0 = False
    go n@(InternedMu _) = not (unconstrained n)
    go (InternedUnion alternatives) = any reachesConstrainedMu (internedUnionMembers alternatives)
    go (Node es) = any (any reachesConstrainedMu . edgeChildren) es
    go _ = False
{-# INLINEABLE reachesConstrainedMu #-}
{-# SPECIALIZE reachesConstrainedMu :: Node Symbol -> Bool #-}

-- | Table for 'reachesConstrainedMu'.
reachesConstrainedMuCache :: TypeableMemoCache
reachesConstrainedMuCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE reachesConstrainedMuCache #-}

-- | Table for 'provablyEmpty'.
provablyEmptyCache :: TypeableMemoCache
provablyEmptyCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE provablyEmptyCache #-}

{- | Whether a closed node provably accepts no term. False proves nothing.

The check reads conjunctions: sets of nodes that one term must be in. A
conjunction can accept a term when one of its edge tuples can. An edge tuple
has one edge of each node, all with one symbol and one arity, and the classes
of the equalities of all its edges. It can accept a term when, at each child
position, the conjunction of the children of its edges can, and, for each
class, the conjunction of the nodes at the paths of the class can: the
subterm that the class shares is in each of them. The check takes the least
fixed point of this rule over the conjunctions that the node reaches. A
conjunction beyond 'emptinessBudget' of them, and a conjunction with free
references, counts as one that can accept a term. So true is never wrong.

The check builds no intersection. The intersection of an intersection is a
new node, deeper in recursive nodes than its operands, and the cost of an
intersection grows with that depth. Two conjunctions of the same nodes are
one conjunction, so a class that needs a conjunction again closes the fixed
point.

Emptiness is not decidable for every automaton with path equalities, so the
check cannot find every empty node. It finds a class whose intersection needs
the node again, with no other way to a term.
-}
{-# INLINEABLE provablyEmpty #-}
provablyEmpty :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Bool
provablyEmpty = memoTypeableWith @symbol provablyEmptyCache $ \start ->
    -- For each conjunction that the check reads, the requirements of each edge tuple.
    let rows = explore emptinessBudget Map.empty [[start]]
     in null (freeVars start) && not (canAccept rows (grow rows Set.empty) [start])
  where
    explore :: Int -> Map.Map [Int] [[[Node symbol]]] -> [[Node symbol]] -> Map.Map [Int] [[[Node symbol]]]
    explore _ seen [] = seen
    explore budget seen (ns : rest)
        | EmptyNode `elem` ns = explore budget seen rest
        | budget <= 0 || not (all (null . freeVars) ns) || Map.member (keys ns) seen = explore budget seen rest
        | otherwise = explore (budget - 1) (Map.insert (keys ns) tupleRows seen) (concat tupleRows <> rest)
      where
        tupleRows =
            [ requirements classes (map edgeChildren tuple)
            | tuple <- edgeTuples ns
            , let classes = foldr (combineEqConstraints . equalities . edgeConstraint) EmptyConstraints tuple
            , classes /= EqContradiction
            ]

    edgeTuples [] = []
    edgeTuples (n : ns) = foldr extend [[e] | e <- nodeEdges n] ns
      where
        extend m tuples =
            [ e : tuple
            | tuple@(first : _) <- tuples
            , e <- nodeEdges m
            , edgeSymbol e == edgeSymbol first
            , length (edgeChildren e) == length (edgeChildren first)
            ]

    requirements classes childLists =
        map conjunction (transpose childLists)
            <> [ conjunction [getPath p children | children <- childLists, p <- Set.toList (unPathEClass pec)]
               | pec <- unsafeGetEclasses classes
               ]

    -- The nodes in the order of their identities, each once. A conjunction
    -- with an empty node accepts nothing, so it is the empty node alone.
    conjunction ns
        | EmptyNode `elem` ns = [EmptyNode]
        | otherwise = IntMap.elems $ IntMap.fromList [(key n, n) | n <- ns]

    grow rows known =
        let next = Map.keysSet $ Map.filter (any (all (canAccept rows known))) rows
         in if next == known then known else grow rows next

    canAccept rows known ns
        | EmptyNode `elem` ns = False
        | otherwise = not (all (null . freeVars) ns) || Map.notMember (keys ns) rows || Set.member (keys ns) known

    keys = map key
    key n = let NodeId ident = nodeIdentity n in ident

-- | The number of conjunctions that 'provablyEmpty' reads before it stops.
emptinessBudget :: Int
emptinessBudget = 1000

{- | The edges of each node that a root reaches, in the order of enumeration:
by arity, then by symbol, then by the canonical classes of their children
('canonicalClasses'), then by their equalities and guard. The classes depend
on the content of the graph only, so the order does not depend on the
automata that the process built before. Two edges that are equal in all of
these have children in the same classes, so they give the same terms in the
same order.
-}
canonicalOrder :: (Hashable symbol, Ord symbol, Typeable symbol) => Node symbol -> IntMap.IntMap [Edge symbol]
canonicalOrder root = IntMap.map (sortOn key) graph
  where
    graph = reachable root
    classes = canonicalClasses $ IntMap.map (map $ \edge -> (shape edge, map nodeIdentity $ edgeChildren edge)) graph
    shape edge = (length $ edgeChildren edge, edgeSymbol edge, constraintEqualities constraint, constraintGuard constraint)
      where
        constraint = edgeConstraint edge
    key edge = (arity, symbol, [classes IntMap.! child | NodeId child <- map nodeIdentity $ edgeChildren edge], equalities', guard')
      where
        (arity, symbol, equalities', guard') = shape edge

{- | Order edges by descending weight. The sort is stable, so edges with
equal weights keep their order.
-}
byWeight :: (Edge symbol -> Double) -> [Edge symbol] -> [Edge symbol]
byWeight weight = sortOn (Down . weight)

-- | Table for 'canonicalEdges'.
canonicalEdgesCache :: TypeableMemoCache
canonicalEdgesCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE canonicalEdgesCache #-}

{- | The edges of a node in 'canonicalOrder', for a node that the enumeration
builds, such as an intersection or an unfolding.
-}
canonicalEdges :: forall symbol. (Hashable symbol, Ord symbol, Typeable symbol) => Node symbol -> [Edge symbol]
canonicalEdges = memoTypeableWith @symbol canonicalEdgesCache $ \n ->
    let NodeId ident = nodeIdentity n in canonicalOrder n IntMap.! ident

{- | The edges of each node in the order of 'runs': 'canonicalOrder' of the
graph that the root reaches, then by the weights of 'runsBy', if any. A node
that the enumeration builds gets its edges from 'canonicalEdges'.
-}
canonicalEdgesOf ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Maybe (Edge symbol -> Double) -> Node symbol -> Node symbol -> [Edge symbol]
canonicalEdgesOf weights root = edgesOf
  where
    byWeights = maybe id byWeight weights
    ordered = IntMap.map byWeights (canonicalOrder root)
    edgesOf n =
        let NodeId ident = nodeIdentity n
         in fromMaybe (byWeights (canonicalEdges n)) (IntMap.lookup ident ordered)

-- | Enumerate one node under the suspended constraints currently in scope.
enumerateNode ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
enumerateNode _ EmptyNode = mzero
enumerateNode scs n =
    let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
     in case hereConstraints of
            Sequence.Empty -> case n of
                Mu _ -> TermFragmentUVar <$> addUVarValue (Just n)
                InternedUnion _ -> TermFragmentUVar <$> addUVarValue (Just n)
                Node _ -> do
                    edgesOf <- gets _edgesOf
                    enumerateEdge scs =<< branches (edgesOf n)
                Rec recId ->
                    error $
                        "enumerateNode: unexpected unresolved recursive reference "
                            <> show recId
                            <> " for symbol type "
                            <> show (typeRep @symbol)
            (x :<| xs) -> do
                reps <- mapM (getUVarRepresentative . scGetUVar) hereConstraints
                forM_ xs $ \sc ->
                    modify' $ \s ->
                        s{_uvarRepresentative = UnionFind.union (scGetUVar x) (scGetUVar sc) (_uvarRepresentative s)}
                uv <- getUVarRepresentative (scGetUVar x)
                -- The waiting counts of the old representatives go to the new one.
                let merged = IntSet.delete (uvarToInt uv) (IntSet.fromList (map uvarToInt (Foldable.toList reps)))
                    move waiting old = case IntMap.lookup old waiting of
                        Just waits -> IntMap.insertWith (+) (uvarToInt uv) waits (IntMap.delete old waiting)
                        Nothing -> waiting
                modify' $ \s -> s{_waitingUVars = IntSet.foldl' move (_waitingUVars s) merged}
                mapM_ (assimilateUvarVal uv) reps

                mergeNodeIntoUVarVal uv n descendantConstraints
                return $ TermFragmentUVar uv

-- | Enumerate one edge, introducing UVars for its equality classes.
enumerateEdge ::
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Edge symbol -> EnumerateM symbol (TermFragment symbol)
enumerateEdge = enumerateEdgeWith enumerateNode

-- | Prepare the children of one selected edge with the supplied function.
enumerateEdgeWith ::
    (Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)) ->
    Seq SuspendedConstraint ->
    Edge symbol ->
    EnumerateM symbol (TermFragment symbol)
enumerateEdgeWith prepareChild scs e = do
    let inherited = descendScs IntMap.empty scs
    -- The inherited obligations must fit the edge. Its own classes fit it.
    guard $ maybe True (\(highest, _) -> compareLength (edgeChildren e) highest == GT) (IntMap.lookupMax inherited)

    newScs <- mapM pecToSuspendedConstraint (unsafeGetEclasses $ equalities $ edgeConstraint e)
    let children = descendScs inherited newScs
    fragment <-
        TermFragmentNode (edgeSymbol e)
            <$> zipWithM (\i n -> prepareChild (IntMap.findWithDefault Sequence.Empty i children) n) [0 ..] (edgeChildren e)
    when (residual (edgeConstraint e)) $
        modify' $
            \s -> s{_obligations = (edgeConstraint e, fragment) : _obligations s}
    return fragment

{- | Expand one ordinary node and defer its eligible children.
Keep the existing preparation of terminal equality endpoints and recursive
boundaries. A selected root must not defer itself into another fresh slot.
-}
enumerateShallowHere ::
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
enumerateShallowHere scs n@(Node _)
    | not (any (isTerminalPathTrie . scGetPathTrie) scs) = do
        edgesOf <- gets _edgesOf
        enumerateEdgeWith prepareShallowChild scs =<< branches (edgesOf n)
enumerateShallowHere scs n = enumerateNode scs n

{- | Keep an ordinary child in a slot until the ready-hole loop selects it.
Install its full suspended constraints through the existing waiting counter.
Terminal endpoints still merge through the existing node-preparation path.
-}
prepareShallowChild ::
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
prepareShallowChild scs n@(Node _)
    | not (any (isTerminalPathTrie . scGetPathTrie) scs) = do
        uv <- addUVarValue (Just n)
        setUVarValue uv (UVarUnenumerated (Just n) scs)
        pure (TermFragmentUVar uv)
prepareShallowChild scs n = enumerateNode scs n

---------------------
-------- Enumeration-loop control
---------------------

-- | Result of looking for the next UVar that can be expanded.
data ExpandableUVarResult
    = -- | Candidates exist, but all are blocked by suspended dependencies.
      ExpansionStuck
    | -- | Enumeration has no more UVar work to do.
      ExpansionDone
    | -- | The next unconstrained UVar to expand.
      ExpansionNext !UVar
    deriving (Show)

{- | Find every expandable UVar that no suspended constraint waits for.

The state keeps the expandable slots and the representatives of the UVars
that suspended constraints name. Slots merged into another UVar are marked
'UVarEliminated', so every expandable slot is a representative, and the
blocked ones are the keys of '_waitingUVars'.

'Nothing' means no candidates remain. @Just empty@ means candidates exist, but
all of them are blocked by suspended constraints.
-}
findExpandableUVars :: EnumerateM symbol (Maybe IntSet.IntSet)
findExpandableUVars = do
    candidates <- gets _expandableUVars
    waiting <- gets _waitingUVars
    return $
        if IntSet.null candidates
            then Nothing
            else Just (candidates IntSet.\\ IntMap.keysSet waiting)

{- | Which of the currently expandable UVars to expand next.

The list holds every UVar that can be expanded right now, in the order the
enumerator itself would consider them, so its head is what it would pick.

Returning 'Nothing' means "no preference". Returning a UVar that is not in the
list means the same thing: this steers the order and can never make a UVar
expandable before it is ready.

Use it when a check in the oracle state waits for a hole. Return that hole,
and the check is settled before the enumerator lists the rest of the branch.
-}
type ExpansionOrder state = state -> [UVar] -> Maybe UVar

-- | The 'ExpansionOrder' that always leaves the choice to the enumerator.
noExpansionPreference :: ExpansionOrder state
noExpansionPreference _ _ = Nothing

-- | Find the next UVar that can be expanded without violating dependencies.
nextExpandableUVar :: ([UVar] -> Maybe UVar) -> EnumerateM symbol ExpandableUVarResult
nextExpandableUVar choose = do
    mbCandidates <- findExpandableUVars
    return $ case mbCandidates of
        Nothing -> ExpansionDone
        Just candidates
            | IntSet.null candidates -> ExpansionStuck
            | otherwise ->
                -- The candidate list is only forced if the caller looks at it,
                -- so the default order pays nothing for this.
                ExpansionNext $
                    case choose (map intToUVar $ IntSet.toAscList candidates) of
                        Just preferred
                            | IntSet.member (uvarToInt preferred) candidates ->
                                preferred
                        _ -> intToUVar (IntSet.findMin candidates)

{- | Expand one UVar into a fragment.

The pattern bind is deliberately failable: a failed match in 'EnumerateM'
ends the branch, so a UVar that is not an unexpanded node drops this branch
instead of raising. The branch is unreachable through @enumerateFully'@, which takes its
UVar from 'nextExpandableUVar' and so only offers expandable UVars.
-}
enumerateOutUVar ::
    (Hashable symbol, Typeable symbol) => UVar -> EnumerateM symbol (TermFragment symbol)
enumerateOutUVar = enumerateOutUVarWith enumerateNode

-- | Expand one selected slot with the supplied node-expansion function.
enumerateOutUVarWith ::
    (Hashable symbol, Typeable symbol) =>
    (Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)) ->
    UVar ->
    EnumerateM symbol (TermFragment symbol)
enumerateOutUVarWith expandNode uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv
        ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt uv') . _recursionAncestry
        modify' $ \s ->
            s
                { _expansionAncestry = if recursiveBoundary n then HashSet.insert (recursionKey n scs) ancestry else ancestry
                }

        t <- case n of
            Mu _ -> expandNode scs (unfoldOuterRec n)
            InternedUnion _ -> expandNode scs (Node $ nodeEdges n)
            _ -> expandNode scs n

        modify' $ \s -> s{_expansionAncestry = HashSet.empty}
        setUVarValue uv' (UVarEnumerated t)
        return t

-- | Expand the root UVar until it represents a complete term.
enumerateFully :: (Hashable symbol, Typeable symbol) => EnumerateM symbol ()
enumerateFully =
    enumerateFully' () noExpansionPreference (\state _ _ -> return (False, state))

{- | Enumerate until the root term is complete, with optional oracle pruning.

The oracle is called twice around each UVar it expands:

* @Right node@ is passed before expanding the node, so callers can drop a
  whole branch early when the node about to be expanded is already known to
  be uninteresting.
* @Left fragment@ is passed after expansion, together with the UVar it came
  from, so callers can reject the fragment or update their state before
  enumeration continues.

The threaded state parameter belongs entirely to the caller. Returning @True@
prunes the current nondeterministic branch; returning @False@ keeps it.

The 'ExpansionOrder' sees the same state and may steer which expandable UVar
goes next; 'noExpansionPreference' leaves that to the enumerator. An
unconstrained 'Mu' is never offered for expansion, so it is not expanded and
produces neither callback. Enumeration ends when no other UVar can be expanded.
-}
enumerateFully' ::
    forall symbol a.
    (Hashable symbol, Typeable symbol) =>
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    EnumerateM symbol ()
enumerateFully' ost order oracle = do
    muv <- nextExpandableUVar (order ost)
    case muv of
        ExpansionStuck -> mzero
        ExpansionDone -> return ()
        ExpansionNext uv ->
            let continue ost' = do
                    tf <- enumerateOutUVar uv
                    (should_prune, ost'') <- oracle ost' uv (Left tf)
                    if should_prune
                        then mzero
                        else enumerateFully' ost'' order oracle
                expand n = do
                    (should_prune, ost') <- oracle ost uv (Right n)
                    if should_prune then mzero else continue ost'
             in do
                    UVarUnenumerated (Just n) scs <- getUVarValue uv
                    case n of
                        _ | recursiveBoundary n -> do
                            uv' <- getUVarRepresentative uv
                            ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt uv') . _recursionAncestry
                            if HashSet.member (recursionKey n scs) ancestry
                                then do
                                    -- The expansion of this node with these paths led to it
                                    -- again, so each further expansion repeats the last one.
                                    -- Enumeration stops here, as at an unconstrained 'Mu'.
                                    setUVarValue uv' (UVarUnenumerated (Just n) Sequence.Empty)
                                    enumerateFully' ost order oracle
                                else expand n
                        _ -> expand n

---------------------
-------- Expanding an enumerated term fragment into a term
---------------------

{- | The fragment the root UVar holds, or the root hole itself.

An automaton that is a bare 'Mu' is never expanded, because an unconstrained
'Mu' is where enumeration stops. Its root stays a hole, exactly as a nested one
does.
-}
rootTermFrag :: EnumerateM symbol (TermFragment symbol)
rootTermFrag = do
    value <- getUVarValue root
    return $ case value of
        UVarEnumerated fragment -> fragment
        _ -> TermFragmentUVar root
  where
    root = intToUVar 0

{- | Expand a fragment even if it still contains unenumerated UVars.

Unlike 'expandTermFragWith', which fails on an unenumerated non-recursive node,
this is safe for diagnostics and oracle logging while enumeration is still in
progress. Unexpanded UVars become 'UVarHole's, except a recursive one with no
suspended constraints, which is where enumeration stops and which becomes
'TruncatedRecursion'. A recursive node whose constraints have not been settled
is still pending expansion, so it is reported as a hole. An oracle that parks
checks on holes would otherwise read it as final and settle a check that has not
been decided.
-}
expandPartialTermFrag :: TermFragment symbol -> EnumerateM symbol (Term (PartialSymbol symbol))
expandPartialTermFrag (TermFragmentNode symbol children) =
    Term.traverseNode expandPartialTermFrag (ConcreteSymbol symbol) children
expandPartialTermFrag (TermFragmentUVar uv) = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandPartialTermFrag fragment
        UVarUnenumerated (Just node) Sequence.Empty | recursiveBoundary node -> return $ Term.Node TruncatedRecursion []
        _ -> return $ Term.Node (UVarHole uv) []

-- | Expand a complete term fragment into a concrete term, with the symbol that stands for truncated recursion.
expandTermFragWith :: symbol -> TermFragment symbol -> EnumerateM symbol (Term symbol)
expandTermFragWith recursionSymbol = go
  where
    go (TermFragmentNode s ts) = Term.traverseNode go s ts
    go (TermFragmentUVar uv) = do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> go t
            UVarUnenumerated (Just node) _ | recursiveBoundary node -> return $ Term.Node recursionSymbol []
            _ ->
                error "expandTermFragWith: Non-recursive, unenumerated node encountered"

{- | Expand an enumerated UVar into a concrete term.

A UVar holding an unconstrained 'Mu' was never expanded, and truncates to the
same marker 'expandTermFragWith' gives a nested one. Any other unenumerated
state is not reachable once enumeration reports itself finished, and drops the
branch rather than guessing.
-}
expandUVarWith :: symbol -> UVar -> EnumerateM symbol (Term symbol)
expandUVarWith recursionSymbol uv = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandTermFragWith recursionSymbol fragment
        UVarUnenumerated (Just node) _ | recursiveBoundary node -> return $ Term.Node recursionSymbol []
        _ -> mzero

---------------------
-------- Full enumeration
---------------------

{- | Enumerate terms while retaining truncation explicitly.

Where 'terms' embeds a recursion marker into the caller's alphabet, this
uses 'TruncatedRecursion'. Any genuinely unresolved non-recursive variable remains
a 'UVarHole', as it does in 'expandPartialTermFrag'.
-}
truncatedTerms ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Node symbol -> [Term (PartialSymbol symbol)]
truncatedTerms n = map fst $
    flip allBranches (initEnumerationState (canonicalEdgesOf Nothing n) n) $ do
        enumerateFully
        rootTermFrag >>= expandPartialTermFrag

{- | Enumerate terms while letting an oracle prune branches.

This is the public entry point for pruning-aware enumeration. The oracle has
type:

@
state -> UVar -> Either TermFragment Node -> EnumerateM (Bool, state)
@

It receives the caller state, the UVar being considered, and either the node
about to be expanded (@Right@) or the fragment just produced (@Left@). Return
@True@ to discard that branch, or @False@ with updated state to keep
enumerating. The state is threaded down each nondeterministic branch
separately, so what one branch records cannot leak into a sibling.

The caller decides which terms to reject. This library supplies the callbacks
and the means to read a partial term ('expandPartialTermFrag'). It has no
notion of which shapes are interesting.

A check that cannot be settled because the fragment still holds an unexpanded
'TermFragmentUVar' does not need help from this module either. Park it in the
oracle's own state under that hole's UVar. The oracle is called with
@Left fragment@ for every UVar that enumeration expands, and that UVar is always
a current representative. Enumeration can merge a parked UVar into another one,
and then no call names the parked UVar. So at each call, look up the current
representative of each parked UVar with 'getUVarRepresentative', and settle the
checks whose representative is the UVar of the call. A UVar that holds an
unconstrained 'Mu' gets no call. 'termsPruneWith' can bring a call forward.

Truncated recursion is reported as the @Mu@ marker in the caller's alphabet;
'termsPruneWith' takes that symbol explicitly, so an alphabet without an
'IsString' instance can prune too.
-}
termsPrune ::
    forall symbol a.
    (Hashable symbol, Ord symbol, Typeable symbol, IsString symbol) =>
    a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    Node symbol ->
    [Term symbol]
termsPrune ost oracle = termsPruneWith "Mu" ost noExpansionPreference oracle

{- | 'termsPrune' with an explicit recursion symbol and control over which
UVar is expanded next.

The first argument is the symbol standing for truncated recursion, as in
'termsWith'. The symbol is passed here, not through 'IsString', so an ordinary
datatype alphabet can use the pruning API.

An oracle that parks checks on unexpanded holes can use the 'ExpansionOrder' to
reach those holes sooner: return the candidate the parked checks are waiting
on, and a branch that a check rejects ends before the rest of it is
enumerated.

This is a hint about order, not about which terms are enumerated. It cannot
make a UVar expandable early. For an oracle whose rejections are monotone (a
branch that can be rejected stays rejectable), it changes only how much work is
done. An oracle that decides differently depending on the order in which it
sees UVars sees the difference.
-}
termsPruneWith ::
    forall symbol a.
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    symbol ->
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    Node symbol ->
    [Term symbol]
termsPruneWith recursionSymbol ost order oracle n =
    map fst $ flip allBranches (initEnumerationState (canonicalEdgesOf Nothing n) n) $ do
        enumerateFully' ost order oracle
        expandUVarWith recursionSymbol (intToUVar 0)

{- | The terms of the automaton's accepting runs, each once.

Path equalities are solved by unification. Enumeration stops at a recursive
binder and reports it as the marker term @Mu@ rather than unfolding it;
bound the depth first with 'boundDepth' to see past it, or use 'plainTerms'
and 'plainTermsAtMost' for the depth-ordered listing of an automaton without
constraints. An acyclic automaton with no constraint anywhere is listed level
by level without the enumeration state. A constraint's residual beyond its equalities
is not decided here: use 'runs' to see it with the subterm it guards.

A constraint whose paths descend into a truncated recursive binder is dropped
rather than checked, so a result term containing the marker is not evidence
that the language below it is non-empty.
-}
terms ::
    (Hashable symbol, Ord symbol, Typeable symbol, IsString symbol) =>
    Node symbol -> [Term symbol]
terms = termsWith "Mu"

-- | 'terms' with an explicit symbol for truncated recursion.
termsWith ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    symbol -> Node symbol -> [Term symbol]
termsWith recursionSymbol n
    | plain n = plainTerms n
    | otherwise = dedup $ map fst $ runs recursionSymbol n

-- | Whether the automaton is an acyclic ordinary tree automaton.
plain :: (Typeable symbol) => Node symbol -> Bool
plain n = numNestedMu n == 0 && unconstrained n

{- | The term of every accepting run, with the residual constraints the run
must satisfy, each paired with the complete subterm it guards.

Runs are listed, not distinct terms: an ambiguous automaton yields a term
once per run, and a term is accepted when some run's obligations all hold.
An acyclic automaton with no constraint has no obligations. Its runs are
still listed one by one, so an ambiguous one repeats a term. The symbol
stands for truncated recursion.
-}
runs ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    symbol -> Node symbol -> [(Term symbol, [(Constraint, Term symbol)])]
runs = runsFrom (canonicalEdgesOf Nothing)

{- | 'runs' with a weight for each edge. The enumeration tries the edges of a
node with larger weights first, and edges with equal weights in the order of
'runs'. The weights only change the order of the edges of each node, so the
result has the runs of 'runs', in another order. A weight must not be NaN.
-}
runsBy ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    (Edge symbol -> Double) -> symbol -> Node symbol -> [(Term symbol, [(Constraint, Term symbol)])]
runsBy weight = runsFrom (canonicalEdgesOf (Just weight))

{- | 'runsBy' with a function on the edges of each node, which the
enumeration applies before it tries them. It sees the node of the current
run: in a run, a node that an equality constraint reaches is the
intersection of the nodes of all the paths of its class, because the
enumeration expands it only after all of them. A function that keeps a
subset of the edges keeps a subset of the runs.
-}
runsNarrowedBy ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    (Edge symbol -> Double) ->
    ([Edge symbol] -> [Edge symbol]) ->
    symbol ->
    Node symbol ->
    [(Term symbol, [(Constraint, Term symbol)])]
runsNarrowedBy weight narrowing = runsFrom (\root -> narrowing . canonicalEdgesOf (Just weight) root)

{- | 'runs' in the order of the edges in the automaton, without
'canonicalOrder'. The result has the runs of 'runs', in another order, which
depends on the automata that the process built before. It is for a caller
that sorts the runs itself, and it saves the canonical classes of the graph.
-}
runsInterned ::
    (Hashable symbol, Typeable symbol) =>
    symbol -> Node symbol -> [(Term symbol, [(Constraint, Term symbol)])]
runsInterned = runsFrom (const nodeEdges)

-- | 'runs' with the order of the edges of each node, from the root.
runsFrom ::
    (Hashable symbol, Typeable symbol) =>
    (Node symbol -> Node symbol -> [Edge symbol]) -> symbol -> Node symbol -> [(Term symbol, [(Constraint, Term symbol)])]
runsFrom order recursionSymbol n =
    map fst $ flip allBranches (initEnumerationState (order n) n) $ do
        enumerateFully
        term <- expandUVarWith recursionSymbol (intToUVar 0)
        obligations <- gets _obligations
        pending <- mapM (\(constraint, fragment) -> (constraint,) <$> expandTermFragWith recursionSymbol fragment) obligations
        return (term, pending)

-- | Each term once, in the enumeration order of its first run. The order is kept, unlike a set.
dedup :: (Hashable symbol) => [Term symbol] -> [Term symbol]
dedup = go HashSet.empty
  where
    go _ [] = []
    go seen (t : ts)
        | HashSet.member t seen = go seen ts
        | otherwise = t : go (HashSet.insert t seen) ts

{- | Every term of the underlying ordinary graph of a closed root, ordered by
depth, lazily. Constraints are not interpreted, each term appears once, and a
recursive graph gives an infinite list. See 'terms' for the constrained
listing.
-}
plainTerms ::
    (Hashable symbol, Ord symbol, Typeable symbol) => Node symbol -> [Term symbol]
plainTerms = concat . plainTermLevels

{- | The terms of 'plainTerms' whose leaves are at most the given depth from
the root. A leaf has depth zero, and a negative depth gives no terms. The
deeper terms are never built, so a recursive graph gives a finite list.
-}
plainTermsAtMost ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Depth -> Node symbol -> [Term symbol]
plainTermsAtMost (Depth depth) = concat . genericTake (toInteger depth + 1) . plainTermLevels

-- | The terms of the underlying ordinary graph, grouped by depth.
plainTermLevels ::
    (Hashable symbol, Ord symbol, Typeable symbol) => Node symbol -> [[Term symbol]]
plainTermLevels EmptyNode = []
plainTermLevels root =
    termLevelsBy
        [ (NodeId ident, [(edgeSymbol edge, map nodeIdentity (edgeChildren edge)) | edge <- edges])
        | (ident, edges) <- IntMap.toList (canonicalOrder root)
        ]
        (nodeIdentity root)

{- | Callbacks for ordered pruning with a fixed term key.

All callbacks must be pure and deterministic. They may read partial terms and
compress aliases. They must not allocate UVars, merge classes, enumerate
choices, or restore an earlier equality state. They may update local oracle
state. A rejected branch must stay rejected under every later completion and
shared-state update. Saved UVar references must be resolved in the current
child state before a pending check uses them.

* 'orderedKey' gives the exact key of a complete term. Its meaning must stay
  fixed. The key does not decide residual obligations.
* 'orderedBound' bounds every complete key below the partial root, including
  all remaining raw siblings. 'Nothing' means unknown and retains the work.
  The caller must justify admissibility. A detected invalid bound can occur
  after an earlier output; detection does not establish correct ordering.
* 'orderedRefresh' receives the latest shared state on every queue pop and
  a suspended partial-root action. An unchanged epoch can avoid that action.
  Refresh must install all new checks on prepared sibling sources and queued
  complete runs. Right callbacks are not replayed for a prepared source.
* 'orderedOracle' receives Right before expansion and Left after expansion.
  A true result rejects the branch. A pending Left uses the latest shared
  state and the refreshed parent local state.
* 'orderedOrder' can select only an offered ready UVar. It cannot make a
  blocked UVar ready. The dependency and recursion rules remain in effect.

Shared-state changes may only remove completions. Do not retract an earlier
check when a rewrite-rule basis changes. Keys, the raw automaton, and callback
meaning must stay fixed. Finite raw languages with admissible bounds yield
nondecreasing keys. Equal keys use deterministic queue serials; their order
can differ from eager enumeration. Terms and residual obligations retain
their multiplicities. The caller must decide those obligations.

The cursor uses shallow ordinary-child expansion with the existing equality
state. It keeps recursive ancestry and truncation markers. Equivalence of
every constrained cyclic truncation under a changed expansion order remains
a separate proof obligation. Unknown or weak bounds can require most of a
language before its first certified minimum. No progress or speed bound is
given for an infinite lower-key search.
-}
data OrderedConfig key global local symbol = OrderedConfig
    { orderedBound :: Term (PartialSymbol symbol) -> EnumerateM symbol (Maybe key)
    , orderedKey :: Term symbol -> key
    , orderedRefresh :: global -> local -> EnumerateM symbol (Term (PartialSymbol symbol)) -> EnumerateM symbol (Bool, local)
    , orderedOracle ::
        global -> local -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, local)
    , orderedOrder :: ExpansionOrder local
    }

-- | Callback state for one branch. A raw expansion records its Left event.
data OrderedPhase symbol
    = OrderedAwait
    | OrderedPrepared UVar
    | OrderedLeft UVar (TermFragment symbol)
    | OrderedComplete (Term symbol, [(Constraint, Term symbol)])

-- | One opaque branch from the existing equality enumerator.
data OrderedBranch local symbol = OrderedBranch (EnumerationState symbol) local (OrderedPhase symbol)

{- | Ordered work over immutable branch states and lazy raw sibling sources.
Raw sibling tails retain equality-enumeration state. They do not capture old
shared state or local oracle state. Caller keys and local checks can still
retain data. Queue capacity is not a bound on closure bytes or process RSS.
-}
data OrderedCursor key global local symbol
    = OrderedCursor
        symbol
        (OrderedConfig key global local symbol)
        (Frontier.Cursor key global (OrderedBranch local symbol) (Term symbol, [(Constraint, Term symbol)]))

{- | Committed popped jobs, rejected jobs, pulled siblings, active queue
entries, and maximum queue entries. These counts do not measure closure bytes.
-}
type OrderedStatistics = (Integer, Integer, Integer, Int, Int)

-- | The caller must replenish work or increase frontier capacity.
data OrderedPauseReason = FuelLimit | FrontierLimit
    deriving (Eq, Show)

-- | One complete run, exhaustion, a resumable limit, or an invalid bound.
data OrderedNext key global local symbol
    = OrderedYield (Term symbol, [(Constraint, Term symbol)]) (OrderedCursor key global local symbol)
    | OrderedDone OrderedStatistics
    | OrderedLimit OrderedPauseReason (OrderedCursor key global local symbol)
    | OrderedBadBound key (Maybe key) (OrderedCursor key global local symbol)

-- | Read a hole without enumeration. The read compresses its representative.
getUnexpandedNode :: UVar -> EnumerateM symbol (Maybe (Node symbol))
getUnexpandedNode uv = do
    value <- getUVarValue uv
    pure $ case value of
        UVarUnenumerated node _ -> node
        _ -> Nothing

-- | Start an optional ordered cursor. Keep the eager entry points unchanged.
startOrdered ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    symbol ->
    OrderedConfig key global local symbol ->
    global ->
    local ->
    Node symbol ->
    OrderedCursor key global local symbol
startOrdered marker config global local root =
    let enumState = initEnumerationState (canonicalEdgesOf Nothing root) root
        branch = OrderedBranch enumState local OrderedAwait
     in OrderedCursor marker config (Frontier.start (orderedPolicy marker config) global branch)

-- | Install a stronger shared pruning state. Do not retract old templates.
strengthenOrdered :: global -> OrderedCursor key global local symbol -> OrderedCursor key global local symbol
strengthenOrdered global (OrderedCursor marker config cursor) =
    OrderedCursor marker config (Frontier.strengthen global cursor)

-- | Read logical queue counters. Measure process RSS and residency separately.
orderedStatistics :: OrderedCursor key global local symbol -> OrderedStatistics
orderedStatistics (OrderedCursor _ _ cursor) = orderedCounts (Map.size (Frontier.queue cursor)) (Frontier.counts cursor)

-- | Convert scheduler counters without exposing its private module.
orderedCounts :: Int -> Frontier.Counts -> OrderedStatistics
orderedCounts active current =
    ( Frontier.poppedJobs current
    , Frontier.rejectedJobs current
    , Frontier.pulledSiblings current
    , active
    , Frontier.maximumQueueEntries current
    )

{- | Return the next certified minimum within a work and frontier limit.
'FuelLimit' preserves the cursor. Supply more work to resume. 'FrontierLimit'
also preserves all work. Increase capacity or stop; an unchanged call can
return the same limit. Never treat a limit as exhaustion. Each limit bounds
scheduler entries or steps, not the cost of one raw expansion or observer.
-}
nextOrdered ::
    (Ord key, Hashable symbol, Typeable symbol) =>
    Int -> Int -> OrderedCursor key global local symbol -> OrderedNext key global local symbol
nextOrdered fuel limit (OrderedCursor marker config cursor) =
    let wrap = OrderedCursor marker config
     in case Frontier.next (orderedPolicy marker config) fuel limit cursor of
            Frontier.Yield run remaining -> OrderedYield run (wrap remaining)
            Frontier.Exhausted current -> OrderedDone (orderedCounts 0 current)
            Frontier.Paused reason remaining ->
                OrderedLimit (case reason of Frontier.FuelLimit -> FuelLimit; Frontier.FrontierLimit -> FrontierLimit) (wrap remaining)
            Frontier.InvalidBound key bound remaining ->
                OrderedBadBound key (case bound of Frontier.Unknown -> Nothing; Frontier.Bound value -> Just value) (wrap remaining)

-- | Require a deterministic observer. No result means failure or rejection.
orderedObserve :: EnumerateM symbol a -> EnumerationState symbol -> Maybe (a, EnumerationState symbol)
orderedObserve action enumState = case allBranches action enumState of
    [] -> Nothing
    [result] -> Just result
    _ -> error "ordered enumeration: observer must be deterministic"

-- | Read the partial root without expanding an unresolved node.
orderedPartialRoot :: EnumerateM symbol (Term (PartialSymbol symbol))
orderedPartialRoot = rootTermFrag >>= expandPartialTermFrag

{- | Recheck shared pruning before any callback, expansion, or yield.
Deliver a pending Left event with the current global and refreshed local state.
Keep a prepared source prepared; its original Right callback ran before it
was created. Refresh must install all later global changes for that source.
-}
orderedActivate ::
    symbol ->
    OrderedConfig key global local symbol ->
    global ->
    local ->
    OrderedPhase symbol ->
    EnumerateM symbol (local, OrderedPhase symbol)
orderedActivate marker config global local phase = do
    (reject, updated) <- orderedRefresh config global local orderedPartialRoot
    guard (not reject)
    case phase of
        OrderedLeft uv fragment -> do
            (rejectLeft, after) <- orderedOracle config global updated uv (Left fragment)
            guard (not rejectLeft)
            orderedPrepare marker config global after
        OrderedAwait -> orderedPrepare marker config global updated
        _ -> pure (updated, phase)

{- | Select a ready hole and run its Right callback deterministically.
Keep the existing recursion-key test and completion of residual obligations.
No global callback is put in a raw CPS alternative source.
-}
orderedPrepare ::
    symbol ->
    OrderedConfig key global local symbol ->
    global ->
    local ->
    EnumerateM symbol (local, OrderedPhase symbol)
orderedPrepare marker config global local = do
    choice <- nextExpandableUVar (orderedOrder config local)
    case choice of
        ExpansionStuck -> mzero
        ExpansionDone -> do
            term <- expandUVarWith marker (intToUVar 0)
            obligations <- gets _obligations
            pending <- mapM (\(constraint, fragment) -> (constraint,) <$> expandTermFragWith marker fragment) obligations
            pure (local, OrderedComplete (term, pending))
        ExpansionNext uv -> do
            UVarUnenumerated (Just node) scs <- getUVarValue uv
            let prepare = do
                    (reject, updated) <- orderedOracle config global local uv (Right node)
                    guard (not reject)
                    pure (updated, OrderedPrepared uv)
            if recursiveBoundary node
                then do
                    representative <- getUVarRepresentative uv
                    ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt representative) . _recursionAncestry
                    if HashSet.member (recursionKey node scs) ancestry
                        then do
                            setUVarValue representative (UVarUnenumerated (Just node) Sequence.Empty)
                            orderedPrepare marker config global local
                        else prepare
                else prepare

{- | Expand one prepared hole. This action takes no global, config, or local
state argument. Its raw CPS tail retains only equality-enumeration state.
-}
orderedRawStep ::
    (Hashable symbol, Typeable symbol) => UVar -> EnumerateM symbol (TermFragment symbol)
orderedRawStep = enumerateOutUVarWith enumerateShallowHere

{- | Pull one raw sibling with the parent's refreshed local state.
This source takes no global or config argument. Its child has a pending Left
event, which is delivered only when the child is activated.
-}
orderedSiblings ::
    Frontier.Estimate key ->
    UVar ->
    [(TermFragment symbol, EnumerationState symbol)] ->
    Frontier.Siblings key (OrderedBranch local symbol)
orderedSiblings _ _ [] = Frontier.End
orderedSiblings lower uv ((fragment, enumState) : rest) =
    Frontier.More lower $ \(OrderedBranch _ local _) ->
        (OrderedBranch enumState local (OrderedLeft uv fragment), orderedSiblings lower uv rest)

-- | Connect shared callbacks to the scheduler outside the raw alternative tail.
orderedPolicy ::
    (Hashable symbol, Typeable symbol) =>
    symbol ->
    OrderedConfig key global local symbol ->
    Frontier.Policy key global (OrderedBranch local symbol) (Term symbol, [(Constraint, Term symbol)])
orderedPolicy marker config =
    Frontier.Policy
        { Frontier.refresh = \global (OrderedBranch enumState local phase) ->
            case orderedObserve (orderedActivate marker config global local phase) enumState of
                Just ((updated, phase'), enumState') -> Just (OrderedBranch enumState' updated phase')
                Nothing -> Nothing
        , Frontier.lowerBound = bound
        , Frontier.advance = \branch@(OrderedBranch enumState _ phase) -> case phase of
            OrderedComplete run -> Frontier.Finished run
            OrderedPrepared uv ->
                Frontier.Children (orderedSiblings (bound branch) uv (allBranches (orderedRawStep uv) enumState))
            _ -> error "ordered enumeration: branch was not prepared"
        , Frontier.exactKey = orderedKey config . fst
        }
  where
    bound (OrderedBranch enumState _ phase) = case phase of
        OrderedComplete (term, _) -> Frontier.Bound (orderedKey config term)
        _ -> case orderedObserve (orderedPartialRoot >>= orderedBound config) enumState of
            Just (Just key, _) -> Frontier.Bound key
            _ -> Frontier.Unknown
