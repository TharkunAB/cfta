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
import Data.List (compareLength, genericTake, sortOn)
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
    isTerminalPathTrie,
    unPathEClass,
    unsafeGetEclasses,
 )
import Data.CFTA.Index (Depth (..))
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

A node can accept a term when one of its edges can. An edge can when each of
its children can, and, for each equality class, the intersection of the
nodes at the paths of the class can: the subterm that the class shares is in
each of them. The check takes the least fixed point of this rule over the
nodes that the node reaches through children and these intersections. A node
beyond 'emptinessBudget' of them, and a node with free references, counts as
a node that can accept a term. So true is never wrong.

Emptiness is not decidable for every automaton with path equalities, so the
check cannot find every empty node. It finds a class whose intersection needs
the node again, with no other way to a term.
-}
{-# INLINEABLE provablyEmpty #-}
provablyEmpty :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Bool
provablyEmpty = memoTypeableWith @symbol provablyEmptyCache $ \start ->
    -- For each node that the check reads, the requirements of each edge.
    let rows = explore emptinessBudget IntMap.empty [start]
     in null (freeVars start) && not (canAccept rows (grow rows IntSet.empty) start)
  where
    explore :: Int -> IntMap.IntMap [[Node symbol]] -> [Node symbol] -> IntMap.IntMap [[Node symbol]]
    explore _ seen [] = seen
    explore budget seen (n : rest)
        | EmptyNode <- n = explore budget seen rest
        | budget <= 0 || not (null (freeVars n)) || IntMap.member (key n) seen = explore budget seen rest
        | otherwise = explore (budget - 1) (IntMap.insert (key n) edgeRows seen) (concat edgeRows <> rest)
      where
        edgeRows =
            [ requirements (equalities (edgeConstraint e)) (edgeChildren e)
            | e <- nodeEdges n
            , equalities (edgeConstraint e) /= EqContradiction
            ]

    requirements classes children =
        children
            <> [foldr1 intersect [getPath p children | p <- Set.toList (unPathEClass pec)] | pec <- unsafeGetEclasses classes]

    grow rows known =
        let next = IntMap.keysSet $ IntMap.filter (any (all (canAccept rows known))) rows
         in if next == known then known else grow rows next

    canAccept _ _ EmptyNode = False
    canAccept rows known n = not (null (freeVars n)) || IntMap.notMember (key n) rows || IntSet.member (key n) known

    key n = let NodeId ident = nodeIdentity n in ident

-- | The number of nodes that 'provablyEmpty' reads before it stops.
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
enumerateEdge scs e = do
    let inherited = descendScs IntMap.empty scs
    -- The inherited obligations must fit the edge. Its own classes fit it.
    guard $ maybe True (\(highest, _) -> compareLength (edgeChildren e) highest == GT) (IntMap.lookupMax inherited)

    newScs <- mapM pecToSuspendedConstraint (unsafeGetEclasses $ equalities $ edgeConstraint e)
    let children = descendScs inherited newScs
    fragment <-
        TermFragmentNode (edgeSymbol e)
            <$> zipWithM (\i n -> enumerateNode (IntMap.findWithDefault Sequence.Empty i children) n) [0 ..] (edgeChildren e)
    when (residual (edgeConstraint e)) $
        modify' $
            \s -> s{_obligations = (edgeConstraint e, fragment) : _obligations s}
    return fragment

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
enumerateOutUVar uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv
        ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt uv') . _recursionAncestry
        modify' $ \s ->
            s
                { _expansionAncestry = if recursiveBoundary n then HashSet.insert (recursionKey n scs) ancestry else ancestry
                }

        t <- case n of
            Mu _ -> enumerateNode scs (unfoldOuterRec n)
            InternedUnion _ -> enumerateNode scs (Node $ nodeEdges n)
            _ -> enumerateNode scs n

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
