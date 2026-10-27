{-# LANGUAGE PatternSynonyms #-}

{- | E-graphs with sorts, and how they are tree automata.

An e-graph holds a set of terms and an equivalence of these terms that is a
congruence: when two terms are equal, the terms that differ only in them
are equal too. An e-class is a set of equal terms. An e-node is a symbol
with an e-class for each child. Each e-node has one e-class, and two e-nodes
with the same symbol and children are the same e-node (the hash-cons). The
e-graph follows egg (Willsey et al., POPL 2021): a hash-cons, a union-find
of e-classes, and rebuilding, which restores the congruence after merges.

Each e-class has a sort, or no sort. A sort is a term over sort symbols,
such as a type. The sort is part of the identity of an e-node, so the
constant @[]@ of sort @[Int]@ and the constant @[]@ of sort @[Bool]@ are two
e-nodes. Two e-classes of different sorts do not merge. Sorts are
hash-consed as well, and they never merge. egglog has sorts in the same way.

The e-graph is a persistent value, so a caller can keep an old version.

= Example

The smallest term that a term equals under some rules, and whether the
rules make two terms equal. With @OverloadedStrings@, a string is a
pattern variable. A language without sorts has the sort type @()@.

> data Op = Add | Mul | One | Var String
>     deriving (Eq, Ord, Show, Generic, Hashable)
>
> rules :: [Rule () Op]
> rules =
>     equation (add "x" "y") (add "y" "x")
>         ++ equation (mul "x" (add "y" "z")) (add (mul "x" "y") (mul "x" "z"))
>         ++ [rewrite (mul "x" (PNode One [])) "x"]
>   where
>     add a b = PNode Add [a, b]
>     mul a b = PNode Mul [a, b]
>
> smallest :: Term Op -> Maybe (Int, Term Op)
> smallest t =
>     let (c, g) = addTerm t (emptyEGraph :: EGraph () Op)
>         (g', _) = saturate defaultLimits rules g
>      in extract (\_ sizes -> 1 + sum sizes) g' c
>
> equalUnder :: Term Op -> Term Op -> Bool
> equalUnder a b =
>     let (ca, g1) = addTerm a (emptyEGraph :: EGraph () Op)
>         (cb, g2) = addTerm b g1
>      in reportStop (snd (saturateUntilEqual defaultLimits rules ca cb g2)) == Equal

'saturateWith' takes a 'Saturation': an e-class analysis, such as constant
folding, on whose data a rule can have a condition such as
@holds "x" (/= Just 0)@, and two e-classes to make equal. 'addTermWith'
adds terms with sorts, such as typed terms.

= E-graphs are tree automata

An e-graph is a bottom-up deterministic tree automaton (Pollock and Haan, in
Wang et al., "E-Graphs, VSAs, and Tree Automata: a Rosetta Stone", EGRAPHS
2022; Suciu, Wang and Zhang, "Semantic Foundations of Equality Saturation",
ICDT 2025):

* An e-class is a state.
* An e-node @f(c1, ..., cn)@ of the e-class @c@ is a transition
  @f(c1, ..., cn) -> c@.
* The hash-cons makes the automaton deterministic: one left side of a
  transition has one state.
* Rebuilding keeps the automaton deterministic after a merge: when two
  transitions become the same, their states merge. This is the congruence.

So the terms of an e-class are the language of its state. A general FTA has
no hash-cons: two transitions with one left side can have two states. A
version space algebra is an acyclic FTA.

An ECTA (Koppel et al., ICFP 2022) adds equality constraints to the
transitions of an FTA: the subterms at some paths must be equal. With
equality constraints, an automaton describes some sets of terms with far
fewer states, and some infinite sets that no FTA describes, such as the
terms @f(t, t)@.

= The e-graph is an ECTA with a union-find

This module keeps an e-graph as an ECTA of cfta, 'FTA.FTA' with a
'Constraint' on each transition, and adds what the automaton does not have:

* The automaton is the store. Each root e-class is a state, and its e-nodes
  are the transitions of the state. The sort of an e-node is the sort of
  its state: two e-classes of different sorts do not merge. After
  'rebuild', each child of a transition is a root, so the table is the
  table of a valid automaton, and 'classAutomaton' is that automaton with
  the rows that the state of an e-class reaches. "Data.CFTA.Sized" in
  @cfta-generator@ counts, lists, ranks, unranks, and samples its terms,
  and 'termsByCost' lists them in the order of a cost.
* The union-find is the union-find of cfta that the enumeration of an ECTA
  uses for its equalities ("Data.CFTA.Internal.UnionFind"). A merge is a
  union of two states, and their rows join.
* The hash-cons is the inverse of the transitions: from the left side of a
  transition to its state. It keeps the automaton deterministic, and
  'rebuild' restores the determinism after merges. This is the congruence.

An e-node can have an equality constraint on its transition, as in an ECTA
('addConstrained'). The terms of an e-class are equal to each other, so a
constraint does not change which e-classes are equal: the hash-cons, the
users, and the matcher see the plain form of the e-node. The constraint
changes which terms the e-class has. Equality constraints also occur in
patterns: a pattern in which a variable occurs twice, such as @x + x@,
accepts the terms whose subterms at the two paths of @x@ are equal, and a
sort variable that occurs twice is an equality constraint between the paths
of the sorts.

= E-matching is an intersection

The matches of a pattern are the terms of the product of the e-graph
automaton and the automaton of the pattern that satisfy the equality
constraints of the pattern. 'ematchByIntersection' computes the matches by
this definition, with 'FTA.intersectWith'. 'ematch' and the saturation
explore the same product from a few roots, one run at a time, and check the
equality constraints as they bind the variables. The test suite checks that
the two give the same matches.

= Saturation

Each iteration of a saturation matches the rules, applies the matches, and
rebuilds, as egg does. Three things make it cheaper than matching every rule
at every e-class:

* A rule starts at the e-classes of the symbol of its left side with the
  fewest e-classes, and walks up through the users of each e-class to the
  roots. In a curried encoding, every application has the same symbol, and
  the head of the application decides.
* Each e-class has the stamp of its last change. A match that passes no
  e-class newer than the last run of its rule is old, and the rule applied it
  then, so the rule finds only the new matches (semi-naive matching, as in
  egglog). When few e-classes changed, the roots come from the paths up from
  them.
* An analysis is an evaluation of the e-graph automaton from the leaves up,
  as 'analyse' computes it; a saturation keeps it up to date from the
  e-classes that changed.

= Refinements

Each term of an e-class has the same value, so a refinement of the value
that one e-node gives holds for the whole e-class, and an analysis can meet
the refinements of the e-nodes of an e-class. This is the model of egglog,
in which an analysis is a function into a lattice with a merge. 'refines'
makes a rule condition of it: the refinement of the e-class of a variable
must imply a formula, and 'Data.CFTA.Refinement.Lattice.latticeImplies'
decides the implication without a solver.
-}
module Data.CFTA.EGraph (
    -- * E-graphs
    EGraph,
    ClassId,
    emptyEGraph,
    addTerm,
    addTermWith,
    addConstrained,
    lookupTerm,
    lookupTermWith,
    find,
    equivalent,
    merge,
    sortOf,
    eClassCount,
    eNodeCount,

    -- * The terms of an e-class
    classAutomaton,
    classAutomatonWith,
    analyse,
    extract,
    termsByCost,

    -- * Patterns and rules
    Pattern (..),
    SortPattern (..),
    Rule,
    RuleError (..),
    rule,
    rewrite,
    equation,
    ematch,
    ematchByIntersection,

    -- * Equality saturation
    Limits (..),
    defaultLimits,
    Stop (..),
    Report (..),
    saturate,
    saturateUntilEqual,

    -- * Analyses, conditions, and goals in a saturation
    Saturation (..),
    defaultSaturation,
    Analysis (..),
    Condition (..),
    holds,
    different,
    refines,
    saturateWith,
    eClasses,
    eNodesOf,
) where

import Control.Monad (foldM)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (rights)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.List (elemIndex, minimumBy, sortOn, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, listToMaybe)
import Data.Ord (comparing)
import Data.String (IsString (..))
import GHC.Stack (HasCallStack)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalitiesHold, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Formula (Formula)
import Data.CFTA.Internal.Tree (termsByCostBy)
import Data.CFTA.Internal.UnionFind (UnionFind, intToUVar, uvarToInt)
import qualified Data.CFTA.Internal.UnionFind as UnionFind
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Refinement.Verdict (Verdict (..))
import Data.CFTA.Term (Term, pattern Node)

-- | The identity of an e-class. 'find' gives the identity of the root of its e-class.
newtype ClassId = ClassId Int
    deriving (Eq, Ord, Show, Hashable)

-- | A sort: its symbol and the identities of its children. The identity 0 is no sort.
data SortNode s = SortNode !s ![Int]
    deriving (Eq)

instance (Hashable s) => Hashable (SortNode s) where
    hashWithSalt salt (SortNode s ks) = salt `hashWithSalt` s `hashWithSalt` ks

{- | An e-node: the identity of its sort, its symbol, and the e-classes of its
children. An e-node with at most two children keeps them unboxed in one
object, so that a key of the memo is small and a lookup follows no list.
'ENode' builds and matches an e-node of any arity.
-}
data ENode f
    = ENode0 !Int !f
    | ENode1 !Int !f !Int
    | ENode2 !Int !f !Int !Int
    | ENodeN !Int !f ![ClassId]
    deriving (Eq)

-- | An e-node as its sort, its symbol, and the list of its children.
pattern ENode :: Int -> f -> [ClassId] -> ENode f
pattern ENode k f cs <- (viewENode -> (k, f, cs))
  where
    ENode k f cs = case cs of
        [] -> ENode0 k f
        [ClassId a] -> ENode1 k f a
        [ClassId a, ClassId b] -> ENode2 k f a b
        _ -> ENodeN k f cs

{-# COMPLETE ENode #-}

viewENode :: ENode f -> (Int, f, [ClassId])
viewENode = \case
    ENode0 k f -> (k, f, [])
    ENode1 k f a -> (k, f, [ClassId a])
    ENode2 k f a b -> (k, f, [ClassId a, ClassId b])
    ENodeN k f cs -> (k, f, cs)
{-# INLINE viewENode #-}

-- | The symbol of an e-node, without the list of its children.
nodeSymbol :: ENode f -> f
nodeSymbol = \case
    ENode0 _ f -> f
    ENode1 _ f _ -> f
    ENode2 _ f _ _ -> f
    ENodeN _ f _ -> f

-- | The child of an e-node at an index, without the list of its children.
nodeChild :: ENode f -> Int -> Maybe ClassId
nodeChild n k = case n of
    ENode1 _ _ a | k == 0 -> Just (ClassId a)
    ENode2 _ _ a b
        | k == 0 -> Just (ClassId a)
        | k == 1 -> Just (ClassId b)
    ENodeN _ _ cs -> cs !? k
    _ -> Nothing

-- | The number of children of an e-node.
nodeArity :: ENode f -> Int
nodeArity = \case
    ENode0 _ _ -> 0
    ENode1{} -> 1
    ENode2{} -> 2
    ENodeN _ _ cs -> length cs

instance (Hashable f) => Hashable (ENode f) where
    hashWithSalt salt = \case
        ENode0 k f -> salt `hashWithSalt` k `hashWithSalt` f
        ENode1 k f a -> salt `hashWithSalt` k `hashWithSalt` f `hashWithSalt` a
        ENode2 k f a b -> salt `hashWithSalt` k `hashWithSalt` f `hashWithSalt` a `hashWithSalt` b
        ENodeN k f cs -> salt `hashWithSalt` k `hashWithSalt` f `hashWithSalt` cs

{- | An e-node as a transition of the automaton of an e-graph. The sort of
an e-node is the sort of its e-class, the state of the transition.
-}
transitionOf :: ENode f -> FTA.Transition ClassId f Constraint
transitionOf (ENode _ f cs) = FTA.Transition f cs noConstraint

-- | A transition of the automaton of an e-graph as an e-node of a sort.
nodeOf :: Int -> FTA.Transition ClassId f Constraint -> ENode f
nodeOf k (FTA.Transition f cs _) = ENode k f cs

-- | The e-nodes of a root, from the automaton of the e-graph.
nodesAt :: EGraph s f -> Int -> [ENode f]
nodesAt g i = maybe [] (\e -> map (nodeOf (classSort e)) (classRow e)) (IntMap.lookup i (classes g))

-- | The transitions of a root, or none for an identity that is not a root.
rowAt :: EGraph s f -> Int -> [FTA.Transition ClassId f Constraint]
rowAt g i = maybe [] classRow (IntMap.lookup i (classes g))

{- | What an e-graph keeps for an e-class: its transitions, its users, the
e-nodes that have the e-class as a child, with their e-classes, its sort,
and its stamp.
-}
data EClass f = EClass
    { classRow :: ![FTA.Transition ClassId f Constraint]
    {- ^ The e-nodes of the e-class as the transitions of its state, in
    the automaton of the e-graph. After 'rebuild', each child is a root, so
    the rows are the rows of a valid automaton.
    -}
    , classUsers :: ![(ENode f, ClassId)]
    , classUserCount :: !Int
    , classSort :: !Int
    , classStamp :: !Int
    -- ^ The 'clock' of the last change: a new e-node or a merge.
    }

{- | An e-graph of terms over the symbols @f@, with sorts over the sort
symbols @s@.
-}
data EGraph s f = EGraph
    { unionFind :: !UnionFind
    {- ^ The e-classes of the identities: the union-find of cfta that the
    enumeration of an ECTA uses for its equalities.
    -}
    , classes :: !(IntMap.IntMap (EClass f))
    {- ^ The roots. With the rows of the e-classes, it is the transition
    table of the automaton of the e-graph.
    -}
    , memo :: !(HashMap.HashMap (ENode f) ClassId)
    {- ^ The e-class of each e-node. After 'rebuild', it has each canonical
    e-node, and it can keep an earlier form of an e-node, which no canonical
    lookup finds.
    -}
    , classCount :: !Int
    -- ^ The size of 'classes'. 'IntMap.size' walks the map.
    , added :: !Int
    -- ^ The e-nodes that 'addNode' made. Each one gets a new e-class.
    , sortIds :: !(HashMap.HashMap (SortNode s) Int)
    , sortNodes :: !(IntMap.IntMap (SortNode s))
    , pending :: ![ClassId]
    -- ^ The roots whose users 'rebuild' must make canonical.
    , clock :: !Int
    -- ^ The iteration of the saturation, for the stamps of the e-classes.
    , constrained :: !Bool
    -- ^ Whether a transition has an equality constraint ('addConstrained').
    }

-- | The e-graph without terms.
emptyEGraph :: EGraph s f
emptyEGraph =
    EGraph
        (UnionFind.withInitialValues [])
        IntMap.empty
        HashMap.empty
        0
        0
        HashMap.empty
        IntMap.empty
        []
        0
        False

-- | The root of the e-class of an identity.
find :: EGraph s f -> ClassId -> ClassId
find g (ClassId i) = ClassId (uvarToInt (UnionFind.root (intToUVar i) (unionFind g)))

-- | Whether two identities are in one e-class.
equivalent :: EGraph s f -> ClassId -> ClassId -> Bool
equivalent g a b = find g a == find g b

canon :: EGraph s f -> ENode f -> ENode f
canon g = \case
    n@(ENode0 _ _) -> n
    ENode1 k f a -> ENode1 k f (root a)
    ENode2 k f a b -> ENode2 k f (root a) (root b)
    ENodeN k f cs -> ENodeN k f (roots cs)
  where
    root i = let ClassId r = find g (ClassId i) in r
    -- Each root is evaluated, so that a key of the memo holds no thunks.
    roots [] = []
    roots (c : rest) = let !r = find g c; !rs = roots rest in r : rs

{- | The canonical form of an e-node whose form changes, or Nothing when
each child is a root. It compares the children only, and makes no e-node
for a canonical one.
-}
recanon :: EGraph s f -> ENode f -> Maybe (ENode f)
recanon g = \case
    ENode0 _ _ -> Nothing
    ENode1 k f a -> let !a' = root a in if a' == a then Nothing else Just (ENode1 k f a')
    ENode2 k f a b ->
        let !a' = root a
            !b' = root b
         in if a' == a && b' == b then Nothing else Just (ENode2 k f a' b')
    n@(ENodeN _ _ cs) -> if all (\c -> find g c == c) cs then Nothing else Just (canon g n)
  where
    root i = let ClassId r = find g (ClassId i) in r

lookupClass :: EGraph s f -> ClassId -> Maybe (EClass f)
lookupClass g c = let ClassId i = find g c in IntMap.lookup i (classes g)

-- | The identity of a sort.
internSort :: (Hashable s) => Term s -> EGraph s f -> (Int, EGraph s f)
internSort (Node s ts) g0 =
    let (ks, g1) = foldr (\t (acc, h) -> let (k, h') = internSort t h in (k : acc, h')) ([], g0) ts
     in internSortNode (SortNode s ks) g1

internSortNode :: (Hashable s) => SortNode s -> EGraph s f -> (Int, EGraph s f)
internSortNode n g = case HashMap.lookup n (sortIds g) of
    Just k -> (k, g)
    Nothing ->
        let k = maybe 1 ((+ 1) . fst) (IntMap.lookupMax (sortNodes g))
         in (k, g{sortIds = HashMap.insert n k (sortIds g), sortNodes = IntMap.insert k n (sortNodes g)})

sortTerm :: EGraph s f -> Int -> Maybe (Term s)
sortTerm g k = case IntMap.lookup k (sortNodes g) of
    Just (SortNode s ks) -> Node s <$> traverse (sortTerm g) ks
    Nothing -> Nothing

-- | The sort of an e-class, or Nothing when it has no sort.
sortOf :: EGraph s f -> ClassId -> Maybe (Term s)
sortOf g c = lookupClass g c >>= sortTerm g . classSort

-- | Add an e-node, and give its e-class.
addNode :: (Hashable f) => ENode f -> EGraph s f -> (ClassId, EGraph s f)
addNode n0 g = case HashMap.lookup n (memo g) of
    Just c -> (find g c, if constrained g then withTransition (find g c) (transitionOf n) g else g)
    Nothing ->
        let c@(ClassId i) = ClassId (added g)
            ENode k _ cs = n
            use = IntMap.adjust (\e -> e{classUsers = (n, c) : classUsers e, classUserCount = classUserCount e + 1})
         in ( c
            , g
                { classes = foldr (\(ClassId j) -> use j) (IntMap.insert i (EClass [transitionOf n] [] 0 k (clock g)) (classes g)) cs
                , memo = HashMap.insert n c (memo g)
                , classCount = classCount g + 1
                , added = added g + 1
                }
            )
  where
    n = canon g n0

{- | The e-graph with a transition in the row of a root, unless the row has
it or the plain form of it, which accepts more terms.
-}
withTransition :: (Eq f) => ClassId -> FTA.Transition ClassId f Constraint -> EGraph s f -> EGraph s f
withTransition c t g
    | any (\u -> u == t || u == plain) row = g
    | otherwise = g{classes = IntMap.adjust (\e -> e{classRow = row ++ [t]}) i (classes g)}
  where
    ClassId i = c
    row = rowAt g i
    plain = t{FTA.transitionConstraint = noConstraint}

{- | Add an e-node whose terms satisfy an equality constraint, as a
transition of an ECTA does, and give its e-class. The e-node has no sort,
and its children are e-classes of the e-graph. Each term of an e-class
equals the others, so a constraint does not change which e-classes are
equal: the e-node is in the e-class of its plain form, and rules match it as
they match its plain form. The constraint changes the terms of the e-class,
which 'classAutomaton' gives with the constraint, until the plain form is
added, which accepts more terms.
-}
addConstrained :: (Hashable f) => Constraint -> f -> [ClassId] -> EGraph s f -> (ClassId, EGraph s f)
addConstrained constraint f cs g0
    | constraint == noConstraint = addNode (ENode 0 f cs) g0
    | otherwise = case HashMap.lookup n (memo g0) of
        Just c -> (find g0 c, withTransition (find g0 c) t g0{constrained = True})
        Nothing ->
            let (c, g1) = addNode n g0
             in (c, g1{classes = IntMap.adjust (\e -> e{classRow = [t]}) (let ClassId i = c in i) (classes g1), constrained = True})
  where
    n = canon g0 (ENode 0 f cs)
    t = (transitionOf n){FTA.transitionConstraint = constraint}

-- | The e-class of a term without sorts, when the e-graph has the term.
lookupTerm :: (Hashable s, Hashable f) => Term f -> EGraph s f -> Maybe ClassId
lookupTerm = lookupTermWith withoutSort

{- | The e-class of a term of any type, when the e-graph has the term. The
function is the function of 'addTermWith'.
-}
lookupTermWith :: (Hashable s, Hashable f) => (t -> (Maybe (Term s), f, [t])) -> t -> EGraph s f -> Maybe ClassId
lookupTermWith view t g = do
    let (sort, f, ts) = view t
    cs <- traverse (\u -> lookupTermWith view u g) ts
    k <- maybe (Just 0) sortIdentity sort
    find g <$> HashMap.lookup (canon g (ENode k f cs)) (memo g)
  where
    sortIdentity (Node s us) = do
        ks <- traverse sortIdentity us
        HashMap.lookup (SortNode s ks) (sortIds g)

-- | Add a term without sorts, and give its e-class.
addTerm :: (Hashable s, Hashable f) => Term f -> EGraph s f -> (ClassId, EGraph s f)
addTerm = addTermWith withoutSort

-- | The view of 'addTermWith' for a term without sorts.
withoutSort :: Term f -> (Maybe (Term s), f, [Term f])
withoutSort (Node f ts) = (Nothing, f, ts)

{- | Add a term of any type, and give its e-class. The function gives the
sort, the symbol, and the children of a term. For example, a term whose
first child is its type:

> addTermWith (\(Node f (ty : ts)) -> (Just ty, f, ts))
-}
addTermWith ::
    (Hashable s, Hashable f) => (t -> (Maybe (Term s), f, [t])) -> t -> EGraph s f -> (ClassId, EGraph s f)
addTermWith view t g0 =
    let (sort, f, ts) = view t
        (cs, g1) = foldr (\u (acc, h) -> let (c, h') = addTermWith view u h in (c : acc, h')) ([], g0) ts
        (k, g2) = maybe (0, g1) (`internSort` g1) sort
     in addNode (ENode k f cs) g2

{- | Merge the e-classes of two identities, and restore the congruence.
Nothing when the e-classes have different sorts.
-}
merge :: (Hashable f) => ClassId -> ClassId -> EGraph s f -> Maybe (EGraph s f)
merge a b g = case union a b g of
    Nothing -> Nothing
    Just (_, g') -> Just (rebuild g')

{- | Merge two e-classes. The congruence waits for 'rebuild'. Nothing when
their sorts differ; True when they were two e-classes.
-}
union :: ClassId -> ClassId -> EGraph s f -> Maybe (Bool, EGraph s f)
union a b g
    | ra == rb = Just (False, g)
    | otherwise = case (IntMap.lookup ia (classes g), IntMap.lookup ib (classes g)) of
        (Just ea, Just eb)
            | classSort ea /= classSort eb -> Nothing
            | otherwise ->
                -- The union-find chooses the root, by the sizes of the e-classes.
                let (bigVar, unionFind') = UnionFind.unionRoots (intToUVar ia) (intToUVar ib) (unionFind g)
                    iBig = uvarToInt bigVar
                    big = ClassId iBig
                    (iSmall, eBig, eSmall) = if iBig == ia then (ib, ea, eb) else (ia, eb, ea)
                    -- A join copies the shorter list of users, by their counts,
                    -- and the row of the smaller set. Each identity made one
                    -- transition, so the size of a set bounds its row, but
                    -- for the transitions with a constraint that
                    -- 'withTransition' adds.
                    users =
                        if classUserCount eSmall <= classUserCount eBig
                            then classUsers eSmall ++ classUsers eBig
                            else classUsers eBig ++ classUsers eSmall
                    joined =
                        EClass
                            (classRow eSmall ++ classRow eBig)
                            users
                            (classUserCount eSmall + classUserCount eBig)
                            (classSort eBig)
                            (clock g)
                 in Just
                        ( True
                        , g
                            { unionFind = unionFind'
                            , classes = IntMap.insert iBig joined (IntMap.delete iSmall (classes g))
                            , classCount = classCount g - 1
                            , pending = big : pending g
                            }
                        )
        _ -> Nothing
  where
    ra@(ClassId ia) = find g a
    rb@(ClassId ib) = find g b

{- | Restore the congruence after 'union', as egg does: make the users of
each changed e-class canonical, and merge the e-classes of users that
become the same e-node.
-}
rebuild :: (Hashable f) => EGraph s f -> EGraph s f
rebuild = go IntSet.empty IntSet.empty
  where
    -- dirty: the e-classes whose transitions can have a child that is not a
    -- root: the merged e-classes, and the e-classes of the users whose form
    -- changed; a user whose form stays has the same form in its row. joined:
    -- the merged e-classes, whose rows a merge joined.
    go dirty joined g0 = case pending g0 of
        -- Each transition that rebuild touched has roots as children and
        -- occurs once in its row, so that the table is a valid automaton.
        [] ->
            let roots = IntSet.fromList [r | i <- IntSet.toList dirty, let ClassId r = find g0 (ClassId i)]
                joinedRoots = IntSet.map (\i -> let ClassId r = find g0 (ClassId i) in r) joined
                tidy r e _ = Just e{classRow = tidyRow g0 (IntSet.member r joinedRoots) (classRow e)}
             in -- One merge of the e-classes with the roots to tidy. The other
                -- subtrees of the e-classes stay shared.
                g0{classes = IntMap.mergeWithKey tidy id (const IntMap.empty) (classes g0) (IntMap.fromSet (const ()) roots)}
        todo ->
            let merged = IntSet.fromList [i | c <- todo, let ClassId i = find g0 c]
                (g', owners) = foldl' (\(h, o) i -> repair h o i) (g0{pending = []}, IntSet.empty) (IntSet.toList merged)
             in go (IntSet.unions [dirty, merged, owners]) (IntSet.union joined merged) g'
    -- A row with roots as children. A transition whose children are roots
    -- stays as it is, and only a joined row or a row with a changed
    -- transition can have a transition twice.
    tidyRow g wasJoined row =
        let (changed, row') = foldr (canonical g) (False, []) row
         in if changed || wasJoined then dedupe row' else row
    canonical g t (changed, rest)
        | all (\c -> find g c == c) cs = (changed, t : rest)
        | otherwise = (True, t{FTA.transitionChildren = map (find g) cs} : rest)
      where
        cs = FTA.transitionChildren t
    -- The transitions once each, in their first order: a plain transition
    -- by its e-node, and a transition with a constraint, which is rare, by
    -- comparison with the kept ones. The e-nodes of a row have one sort, so
    -- the key of an e-node has sort 0.
    dedupe row@[_] = row
    dedupe row = reverse (snd (foldl' keep (HashSet.empty, []) row))
    keep (seen, kept) t
        | FTA.transitionConstraint t == noConstraint =
            let n = nodeOf 0 t in if HashSet.member n seen then (seen, kept) else (HashSet.insert n seen, t : kept)
        | t `elem` kept = (seen, kept)
        | otherwise = (seen, t : kept)
    repair g owners0 i = case IntMap.lookup i' (classes g) of
        Nothing -> (g, owners0)
        Just e ->
            let users = classUsers e
                -- Take the users out of the e-class, then add them again in
                -- canonical form. A user whose form changes leaves the memo;
                -- a user whose form stays keeps its entry, whose e-class is
                -- the e-class of the user. A merge in 'step' can join this
                -- e-class to another one, so the users of the other one stay
                -- in the joined e-class.
                g1 = g{classes = IntMap.insert i' e{classUsers = [], classUserCount = 0} (classes g)}
                Repaired g2 seen owners = foldl' step (Repaired g1 HashMap.empty owners0) users
                step (Repaired h s o) (u, owner@(ClassId j)) =
                    let (u', formChanged) = maybe (u, False) (,True) (recanon h u)
                        m = if formChanged then HashMap.delete u (memo h) else memo h
                        h1 = case HashMap.lookup u' m of
                            Just other -> maybe h{memo = m} snd (union owner other h{memo = m})
                            Nothing -> h{memo = HashMap.insert u' (find h owner) m}
                     in Repaired h1 (HashMap.insert u' (find h1 owner) s) (if formChanged then IntSet.insert j o else o)
                ClassId root = find g2 (ClassId i')
                users' = HashMap.toList seen
             in ( g2
                    { classes =
                        IntMap.adjust
                            (\e' -> e'{classUsers = users' ++ classUsers e', classUserCount = length users' + classUserCount e'})
                            root
                            (classes g2)
                    }
                , owners
                )
      where
        ClassId i' = find g (ClassId i)

{- | An e-class analysis: for each e-class, the merge of the data of its
e-nodes. The data of an e-node comes from its symbol and the data of its
children. This is the least fixed point of an evaluation of the e-graph
automaton from the leaves up, as cfta computes the productive states of an
automaton: an e-class whose e-nodes all need an e-class without data has no
data. The merge must be associative, commutative, and idempotent, and must
change the data of an e-class only finitely often, so that the fixed point
exists: for example the join of a lattice without infinite ascending
chains, or, for a refinement, the meet of a lattice without infinite
descending chains.
-}
analyse :: (Eq d) => (f -> [d] -> d) -> (d -> d -> d) -> EGraph s f -> ClassId -> Maybe d
analyse make combine g = \c -> let ClassId i = find g c in IntMap.lookup i known
  where
    known = fst (analyseFrom make combine g IntMap.empty (IntMap.keys (classes g)))

{- | The fixed point of an analysis from a table of the data of e-classes and
a worklist of the e-classes whose data can change, and the e-classes whose
data changed. Each e-class of the worklist gets the merge of the data of its
e-nodes whose children have data, and of its earlier data. A change of an
e-class sends only its users, e-node by e-node, to the worklist, as egg does:
the data only grows, so the other e-nodes give nothing new.
-}
analyseFrom ::
    (Eq d) => (f -> [d] -> d) -> (d -> d -> d) -> EGraph s f -> IntMap.IntMap d -> [Int] -> (IntMap.IntMap d, IntSet.IntSet)
analyseFrom make combine g known0 todo = go IntSet.empty known0 (map Whole (IntSet.toAscList (IntSet.fromList roots)))
  where
    roots = [r | i <- todo, let ClassId r = find g (ClassId i)]
    go changed known [] = (known, changed)
    go changed known (task : rest) = case task of
        Whole i
            | IntMap.member i (classes g) ->
                step i [(f, cs) | FTA.Transition f cs _ <- rowAt g i]
            | otherwise -> go changed known rest
        Use (ENode _ f cs) owner -> let ClassId i = find g owner in step i [(f, cs)]
      where
        dataOf c = let ClassId j = find g c in IntMap.lookup j known
        step i nodes = case [make f ds | (f, cs) <- nodes, Just ds <- [traverse dataOf cs]] of
            [] -> go changed known rest
            v : vs ->
                let old = IntMap.lookup i known
                    new' = foldl' combine (maybe v (`combine` v) old) vs
                 in if Just new' == old
                        then go changed known rest
                        else
                            -- The data only grows, so only the users of the
                            -- e-class can get new data.
                            let more = maybe [] (\e -> [Use u o | (u, o) <- classUsers e]) (IntMap.lookup i (classes g))
                             in go (IntSet.insert i changed) (IntMap.insert i new' known) (more ++ rest)

-- The state of a repair in 'rebuild': the e-graph, the users in canonical form, and the e-classes of the users whose form changed.
data Repaired s f = Repaired !(EGraph s f) !(HashMap.HashMap (ENode f) ClassId) !IntSet.IntSet

-- A task of 'analyseFrom': an e-class from all its e-nodes, or one e-node of an e-class.
data Task f = Whole !Int | Use !(ENode f) !ClassId

{- | The cheapest term of an e-class, with its cost. The cost of a term
comes from its symbol and the costs of its children, and must be greater
than each of them, as @1 + sum@ is, so that the cheapest term is finite.
-}
extract :: (Ord c, Eq f) => (f -> [c] -> c) -> EGraph s f -> ClassId -> Maybe (c, Term f)
extract cost g c0 = do
    (k, _) <- best (find g c0)
    term <- build (find g c0)
    Just (k, term)
  where
    costOf = analyse cost min g
    best c = do
        k <- costOf c
        let row = let ClassId j = find g c in rowAt g j
        Just (k, [t | t@(FTA.Transition f cs _) <- row, Just ks <- [traverse costOf cs], cost f ks == k])
    -- The term of the first cheapest transition whose constraint the term satisfies.
    build c = do
        (_, candidates) <- best c
        listToMaybe
            [ term
            | t@(FTA.Transition f cs _) <- candidates
            , Just term <- [Node f <$> traverse (build . find g) cs]
            , equalitiesHold (FTA.transitionConstraint t) term
            ]

{- | The terms of an e-class in the order of a cost, cheapest first, each with
its cost, produced lazily: 'FTA.termsByCost' on the rows of the store, with
the least costs of 'extract'. So the first term has the cost of 'extract'.
The cost must not decrease when the cost of a child grows, and it must be
at least the cost of each child. Then the costs of the list never decrease,
also for a cyclic e-class, whose list is infinite. The terms have no sorts,
as for 'extract'. The automaton of an e-graph is deterministic, so a term
comes once when the e-graph has no sorts; e-nodes that differ only in the
sorts of their children give a term once for each. An e-node with a
constraint gives only the terms that satisfy the constraint, and its plain
form in the same e-class gives all of them.
-}
termsByCost :: (Ord c, Eq f) => (f -> [c] -> c) -> EGraph s f -> ClassId -> [(c, Term f)]
termsByCost cost g c =
    termsByCostBy
        rowOf
        FTA.transitionSymbol
        FTA.transitionChildren
        (equalitiesHold . FTA.transitionConstraint)
        cost
        (analyse cost min g)
        (find g c)
  where
    -- A transition with a constraint whose plain form is in its row gives no
    -- term that the plain form does not give.
    rowOf (ClassId i)
        | constrained g =
            [t | t <- row, FTA.transitionConstraint t == noConstraint || notElem t{FTA.transitionConstraint = noConstraint} row]
        | otherwise = row
      where
        row = rowAt g i

-- | The number of e-classes.
eClassCount :: EGraph s f -> Int
eClassCount = classCount

{- | The number of e-nodes: the canonical e-nodes of all e-classes. It walks
the e-graph. The memo can keep an earlier form of an e-node whose children
merged twice, so its size is not the count.
-}
eNodeCount :: (Hashable f) => EGraph s f -> Int
eNodeCount g = sum [HashSet.size (HashSet.fromList (nodesAt g i)) | i <- IntMap.keys (classes g)]

{- | The terms of an e-class, as an automaton whose states are e-classes.
The sort of a term is the sort of its state. An error is a symbol with two
arities.
-}
classAutomaton :: (Ord f) => EGraph s f -> ClassId -> Either (FTA.FTAError ClassId f) (FTA.FTA ClassId f Constraint)
classAutomaton = classAutomatonWith (\_ f -> f)

-- | 'classAutomaton' with a symbol made from the sort and the symbol of each e-node.
classAutomatonWith ::
    (Ord g) =>
    (Maybe (Term s) -> f -> g) ->
    EGraph s f ->
    ClassId ->
    Either (FTA.FTAError ClassId g) (FTA.FTA ClassId g Constraint)
classAutomatonWith label g c0 = FTA.mkFTA root (go IntSet.empty [root])
  where
    root = find g c0
    -- The rows of the automaton of the e-graph that the state of the e-class
    -- reaches, as 'FTA.trim' keeps them.
    go _ [] = []
    go seen (c@(ClassId i) : rest)
        | IntSet.member i seen = go seen rest
        | otherwise =
            let (sort, row) = maybe (Nothing, []) (\e -> (sortTerm g (classSort e), classRow e)) (IntMap.lookup i (classes g))
             in (c, map (relabel sort) row) : go (IntSet.insert i seen) ([d | t <- row, d <- FTA.transitionChildren t] ++ rest)
    relabel sort (FTA.Transition f cs constraint) = FTA.Transition (label sort f) cs constraint

{- | A pattern: a variable, a symbol with the patterns of its children, or a
pattern whose e-class has a sort. A variable that occurs twice matches one
e-class at both places.
-}
data Pattern s f
    = PVar !String
    | PNode !f ![Pattern s f]
    | PSorted !(SortPattern s) !(Pattern s f)
    deriving (Eq, Show)

-- | A string literal is a variable, so that @PNode Add ["x", "y"]@ is a pattern.
instance IsString (Pattern s f) where
    fromString = PVar

-- | A pattern of a sort: a sort variable, or a sort symbol with the patterns of its children.
data SortPattern s = SVar !String | SNode !s ![SortPattern s]
    deriving (Eq, Show)

-- A compiled sort pattern: the variables are numbers.
data CSort s = CSVar !Int | CSNode !s ![CSort s]

-- A compiled pattern: the variables are numbers, and each node has the sort patterns of its e-class.
data CPat s f = CVar !Int ![CSort s] | CNode !f ![CPat s f] ![CSort s]

{- | A rewrite rule: each instance of the left side is equal to the instance
of the right side with the same variables. Build it with 'rule'.
-}
data Rule s f = Rule
    { ruleLeft :: !(CPat s f)
    , ruleRight :: !(CPat s f)
    , ruleSymbols :: ![f]
    -- ^ The symbols of the left side, once each.
    , ruleAnchors :: ![(f, [(f, Int, Int)])]
    {- ^ The symbol of each node of the left side, and the path to it from
    the root: the symbol, the arity, and the child index of each node above it.
    -}
    , rulePaths :: ![[(f, Int, Int)]]
    -- ^ The path to each node and each variable of the left side.
    , ruleNames :: ![String]
    -- ^ The variables of the left side, by number.
    }

-- | Why a pair of patterns is not a rule.
data RuleError
    = -- | A variable of the right side is not in the left side.
      UnboundVariable !String
    | -- | A sort variable of the right side is not in the left side.
      UnboundSortVariable !String
    deriving (Eq, Show)

{- | A rule from a left and a right side. A node of the right side without a
sort gets the sort of the matched e-class at the root, and no sort below it.
-}
rule :: (Hashable f) => Pattern s f -> Pattern s f -> Either RuleError (Rule s f)
rule left right = do
    let (l, vars, sortVars) = compileLeft left
    r <- compileRight vars sortVars right
    let symbols = HashSet.toList (HashSet.fromList (patternSymbols left))
    pure (Rule l r symbols (anchorsOf l) (pathsOf l) (map fst (sortOn snd (Map.toList vars))))

{- | A rule from a left and a right side, as 'rule' makes it, for a rule that
the program states. It fails with the 'RuleError' when the right side has a
variable or a sort variable that the left side does not have.
-}
rewrite :: (HasCallStack, Hashable f) => Pattern s f -> Pattern s f -> Rule s f
rewrite left right = either (\e -> error ("Data.CFTA.EGraph.rewrite: " ++ show e)) id (rule left right)

{- | The rules of an equation: the direction from each side whose other side
has no other variables. It is empty when each side has a variable that the
other does not have, as in @f x = f y@, so that an equation that a program
finds, such as a law of Specftacular, can give no rule.
-}
equation :: (Hashable f) => Pattern s f -> Pattern s f -> [Rule s f]
equation a b = rights [rule a b, rule b a]

patternSymbols :: Pattern s f -> [f]
patternSymbols (PVar _) = []
patternSymbols (PNode f ps) = f : concatMap patternSymbols ps
patternSymbols (PSorted _ p) = patternSymbols p

anchorsOf :: CPat s f -> [(f, [(f, Int, Int)])]
anchorsOf = go []
  where
    go _ (CVar _ _) = []
    go above (CNode f kids _) = (f, reverse above) : concat [go ((f, length kids, k) : above) kid | (k, kid) <- zip [0 ..] kids]

pathsOf :: CPat s f -> [[(f, Int, Int)]]
pathsOf = go []
  where
    go above (CVar _ _) = [reverse above]
    go above (CNode f kids _) = reverse above : concat [go ((f, length kids, k) : above) kid | (k, kid) <- zip [0 ..] kids]

-- Compile a left side: the pattern, and the numbers of its variables and sort variables.
compileLeft :: Pattern s f -> (CPat s f, Map.Map String Int, Map.Map String Int)
compileLeft p0 = let (c, (vs, ss)) = go [] p0 (Map.empty, Map.empty) in (c, vs, ss)
  where
    go sorts (PSorted sp p) st = let (sp', st') = goSort sp st in go (sp' : sorts) p st'
    go sorts (PVar v) (vs, ss) = case Map.lookup v vs of
        Just i -> (CVar i sorts, (vs, ss))
        Nothing -> let i = Map.size vs in (CVar i sorts, (Map.insert v i vs, ss))
    go sorts (PNode f ps) st0 =
        let (cs, st') = foldl' (\(acc, st) p -> let (c, st1) = go [] p st in (acc ++ [c], st1)) ([], st0) ps
         in (CNode f cs sorts, st')
    goSort (SVar v) (vs, ss) = case Map.lookup v ss of
        Just i -> (CSVar i, (vs, ss))
        Nothing -> let i = Map.size ss in (CSVar i, (vs, Map.insert v i ss))
    goSort (SNode s ps) st =
        let (cs, st') = foldl' (\(acc, st0) p -> let (c, st1) = goSort p st0 in (acc ++ [c], st1)) ([], st) ps
         in (CSNode s cs, st')

-- Compile a right side with the variables of the left side.
compileRight :: Map.Map String Int -> Map.Map String Int -> Pattern s f -> Either RuleError (CPat s f)
compileRight vars sortVars = go []
  where
    go sorts (PSorted sp p) = goSort sp >>= \sp' -> go (sp' : sorts) p
    go sorts (PVar v) = maybe (Left (UnboundVariable v)) (\i -> Right (CVar i sorts)) (Map.lookup v vars)
    go sorts (PNode f ps) = (\cs -> CNode f cs sorts) <$> traverse (go []) ps
    goSort (SVar v) = maybe (Left (UnboundSortVariable v)) (Right . CSVar) (Map.lookup v sortVars)
    goSort (SNode s ps) = CSNode s <$> traverse goSort ps

-- | The e-classes of the variables and the sorts of the sort variables of a match.
data Subst = Subst !(IntMap.IntMap ClassId) !(IntMap.IntMap Int)

-- | Match the sort of an e-class, extending the sort variables.
matchSort :: (Eq s) => EGraph s f -> CSort s -> Int -> IntMap.IntMap Int -> Maybe (IntMap.IntMap Int)
matchSort _ (CSVar v) k b
    | k == 0 = Nothing
    | otherwise = case IntMap.lookup v b of
        Nothing -> Just (IntMap.insert v k b)
        Just k' | k' == k -> Just b
        _ -> Nothing
matchSort g (CSNode s ps) k b = case IntMap.lookup k (sortNodes g) of
    Just (SortNode s' ks) | s == s' -> children ps ks b
    _ -> Nothing
  where
    children (p : ps') (k' : ks') acc = matchSort g p k' acc >>= children ps' ks'
    children [] [] acc = Just acc
    children _ _ _ = Nothing

-- | The e-classes that some e-classes reach through their children.
reach :: EGraph s f -> [ClassId] -> IntMap.IntMap (EClass f)
reach g = go IntMap.empty
  where
    go seen [] = seen
    go seen (c0 : rest)
        | IntMap.member i seen = go seen rest
        | otherwise = case IntMap.lookup i (classes g) of
            Nothing -> go seen rest
            Just e -> go (IntMap.insert i e seen) (foldr (\t more -> FTA.transitionChildren t ++ more) rest (classRow e))
      where
        ClassId i = find g c0

{- | The e-nodes of a root. After each operation that this module exports,
each row has roots as children and each e-node once, so the row is the
answer.
-}
canonicalNodes :: EGraph s f -> Int -> [ENode f]
canonicalNodes = nodesAt

{- | The matches of the left side of a rule in a region: the e-classes and
their canonical e-nodes, closed under children. The match goes down from
each root and carries one substitution, as in egg. This explores the
product of the e-graph automaton and the automaton of the pattern, one run
at a time (see 'ematchByIntersection').

The roots to try come from the symbol of the left side with the fewest
e-classes: from the e-classes with that symbol, the users of each e-class
lead up the path of the symbol to the roots. In a curried encoding, where
each application has the same symbol, this keeps the roots with the right
head.
-}
matchRule ::
    (Eq s, Hashable f) =>
    EGraph s f ->
    IntMap.IntMap (EClass f) ->
    HashMap.HashMap f (Int, [ClassId]) ->
    (Int -> Int) ->
    Int ->
    Maybe IntSet.IntSet ->
    Rule s f ->
    [(ClassId, Subst)]
matchRule g region bySymbol stampOf since changed r =
    foldr
        ( \c rest ->
            down
                (ruleLeft r)
                c
                (Subst IntMap.empty IntMap.empty, since == minBound)
                (\(m, fresh) more -> if fresh then (c, m) : more else more)
                rest
        )
        []
        roots
  where
    -- A match is new when it passes an e-class that changed since the rule
    -- last ran; the rule applied the other matches then.
    seen (ClassId i) fresh = fresh || stampOf i >= since
    -- The matches of a pattern at an e-class go to the continuation, in
    -- front of the rest, so that no list of the matches of a part is made.
    -- Each e-class here is a root: a root of the region, or a child in a
    -- row, which is a root after each exported operation. So two e-classes
    -- are equal when their identities are equal.
    down (CVar v sorts) c (Subst vs ss, fresh) k rest = case sortsFrom c sorts ss of
        Nothing -> rest
        Just ss' -> case IntMap.lookup v vs of
            Nothing -> k (Subst (IntMap.insert v c vs) ss', seen c fresh) rest
            Just c' | c' == c -> k (Subst vs ss', seen c fresh) rest
            _ -> rest
    down (CNode f kids sorts) c@(ClassId i) (Subst vs ss, fresh) k rest = case sortsFrom c sorts ss of
        Nothing -> rest
        Just ss' ->
            let children (child : cs) (kid : ks) m more = down kid child m (\m' more' -> children cs ks m' more') more
                children _ _ m more = k m more
                start = (Subst vs ss', seen c fresh)
             in foldr
                    ( \t more ->
                        let f' = FTA.transitionSymbol t
                         in if f' /= f
                                then more
                                else -- The common arities without a walk of the lengths.
                                    case (FTA.transitionChildren t, kids) of
                                        ([], []) -> k start more
                                        ([a], [p]) -> down p a start k more
                                        ([a, b], [p, q]) -> down p a start (\m more' -> down q b m k more') more
                                        (cs, _) | sameLength cs kids -> children cs kids start more
                                        _ -> more
                    )
                    rest
                    (maybe [] classRow (IntMap.lookup i region))
    sameLength (_ : as) (_ : bs) = sameLength as bs
    sameLength as bs = null as && null bs
    sortsFrom _ [] ss = Just ss
    sortsFrom (ClassId i) sorts ss = do
        e <- IntMap.lookup i (classes g)
        foldM (\b sp -> matchSort g sp (classSort e) b) ss sorts
    -- The roots from the rarest symbol, or, when few e-classes changed, the
    -- roots of the paths up from them: a new match passes a changed e-class.
    roots = case ruleAnchors r of
        [] -> maybe (map ClassId (IntMap.keys region)) deltaRoots changed
        anchors ->
            let (f, steps) = minimumBy (comparing (\(h, _) -> maybe 0 fst (HashMap.lookup h bySymbol))) anchors
                (count, members) = HashMap.lookupDefault (0, []) f bySymbol
             in case changed of
                    Just xs | IntSet.size xs * length (rulePaths r) < count -> deltaRoots xs
                    _ -> map ClassId (IntSet.toAscList (foldr up (IntSet.fromList [i | ClassId i <- members]) steps))
    deltaRoots xs = map ClassId (IntSet.toAscList (IntSet.unions [foldr up xs steps | steps <- rulePaths r]))
    -- The e-classes with an e-node of the step whose child is in the set.
    up (f, n, k) xs =
        IntSet.fromList
            [ j
            | i <- IntSet.toList xs
            , Just e <- [IntMap.lookup i (classes g)]
            , (u, owner) <- classUsers e
            , nodeSymbol u == f
            , nodeArity u == n
            , Just child <- [nodeChild u k]
            , find g child == ClassId i
            , let ClassId j = find g owner
            , IntMap.member j region
            ]

-- | The number of e-classes with each symbol in a region, and the e-classes.
symbolIndex ::
    (Hashable f) => IntMap.IntMap (EClass f) -> HashMap.HashMap f (Int, [ClassId])
symbolIndex region =
    HashMap.map (\cs -> (length cs, cs)) $
        HashMap.fromListWith
            (++)
            [ (f, [ClassId i])
            | (i, e) <- IntMap.toList region
            , f <- HashSet.toList (HashSet.fromList [f' | FTA.Transition f' _ _ <- classRow e])
            ]

{- | The matches of a pattern: the e-class of each instance, and the e-class
of each variable.
-}
ematch :: (Eq s, Hashable f) => EGraph s f -> Pattern s f -> [(ClassId, Map.Map String ClassId)]
ematch g p = case rule p p of
    Left _ -> []
    Right r ->
        let region = classes g
         in [ (c, Map.fromList [(v, vs IntMap.! i) | (i, v) <- zip [0 ..] (ruleNames r)])
            | (c, Subst vs _) <- matchRule g region (symbolIndex region) (const 0) minBound Nothing r
            ]

{- | Build the right side of a rule for a match, or Nothing when the
substitution has no sort for a sort variable.
-}
instantiate :: (Hashable s, Hashable f) => Subst -> Int -> CPat s f -> EGraph s f -> Maybe (ClassId, EGraph s f)
instantiate (Subst vs ss) rootSort pat g0 = case pat of
    CVar v _ -> (\c -> (c, g0)) <$> IntMap.lookup v vs
    -- The root has the sort of the matched e-class, or the merge fails.
    CNode f kids sorts
        | all (\sp -> isJust (matchSort g0 sp rootSort ss)) sorts -> do
            (cs, g1) <- children kids g0
            Just (addNode (ENode rootSort f cs) g1)
        | otherwise -> Nothing
  where
    children [] g = Just ([], g)
    children (kid : rest) g = do
        (c, g1) <- node kid g
        (cs, g2) <- children rest g1
        Just (c : cs, g2)
    node (CVar v _) g = (\c -> (c, g)) <$> IntMap.lookup v vs
    node (CNode f kids sorts) g = do
        (cs, g1) <- children kids g
        (k, g2) <- case sorts of
            sp : _ -> sortOfPattern sp g1
            [] -> Just (0, g1)
        Just (addNode (ENode k f cs) g2)
    sortOfPattern (CSVar v) g = (\k -> (k, g)) <$> IntMap.lookup v ss
    sortOfPattern (CSNode s ps) g = do
        (ks, g1) <- sortChildren ps g
        Just (internSortNode (SortNode s ks) g1)
    sortChildren [] g = Just ([], g)
    sortChildren (p : ps) g = do
        (k, g1) <- sortOfPattern p g
        (ks, g2) <- sortChildren ps g1
        Just (k : ks, g2)

{- | The limits of a saturation. No limit is time, so the result does not
depend on the load.
-}
data Limits = Limits
    { limitIterations :: !Int
    -- ^ The iterations of matching, rewriting, and rebuilding.
    , limitNodes :: !Int
    -- ^ The e-nodes that the saturation may add.
    , limitMatches :: !Int
    {- ^ The backoff of egg: a rule with more matches than its limit in an
    iteration sits out for some iterations, and then has twice the limit and
    twice the ban. 0 is no backoff.
    -}
    }
    deriving (Eq, Show)

-- | The limits of egg: 30 iterations, 10,000 e-nodes, and a backoff from 1,000 matches.
defaultLimits :: Limits
defaultLimits = Limits 30 10000 1000

-- | Why a saturation stopped.
data Stop
    = -- | No rule adds an e-node or merges two e-classes.
      Saturated
    | IterationLimit
    | NodeLimit
    | -- | The two e-classes of 'saturateUntilEqual' are one e-class.
      Equal
    deriving (Eq, Show)

-- | The result of a saturation: its iterations, the e-nodes that it added, and why it stopped.
data Report = Report {reportIterations :: !Int, reportNodes :: !Int, reportStop :: !Stop}
    deriving (Eq, Show)

-- | Apply the rules to the whole e-graph until nothing changes or a limit stops it.
saturate :: (Hashable s, Hashable f) => Limits -> [Rule s f] -> EGraph s f -> (EGraph s f, Report)
saturate limits rules = run limits rules Nothing

{- | An e-class analysis for a saturation, as in egg: the data of an e-node
from its symbol and the data of its children ('analysisMake'), the merge of
the data of the e-nodes of one e-class ('analysisMerge', the @merge@ of egg
and egglog), and a leaf that an e-class with some data equals
('analysisLeaf'), such as the constant that the data is (the constant
folding of egg).
-}
data Analysis f d where
    -- The equality of the data, so that a saturation without an analysis
    -- needs no type of data.
    Analysis ::
        (Eq d) =>
        { analysisMake :: f -> [d] -> d
        , analysisMerge :: d -> d -> d
        , analysisLeaf :: d -> Maybe f
        } ->
        Analysis f d

{- | The condition of a rule on a match. 'Condition' gives it from the
e-graph, the data of each e-class, and the e-class of each variable of the
rule. Conditions combine with '<>', which requires both, and 'mempty' is no
condition. A condition on a variable that the rule does not have is false:

> holds "x" (/= Just 0) <> different "x" "y"
-}
newtype Condition s f d = Condition (EGraph s f -> (ClassId -> Maybe d) -> (String -> Maybe ClassId) -> Bool)

instance Semigroup (Condition s f d) where
    Condition p <> Condition q = Condition (\g dataOf var -> p g dataOf var && q g dataOf var)

instance Monoid (Condition s f d) where
    mempty = Condition (\_ _ _ -> True)

{- | The condition that the data of the e-class of a variable satisfies a
predicate. An e-class without data does not satisfy it.
-}
holds :: String -> (d -> Bool) -> Condition s f d
holds x p = Condition (\_ dataOf var -> maybe False p (var x >>= dataOf))

-- | The condition that two variables are in different e-classes.
different :: String -> String -> Condition s f d
different x y = Condition $ \g _ var -> case (var x, var y) of
    (Just a, Just b) -> not (equivalent g a b)
    _ -> False

{- | The condition that the refinement of the e-class of a variable implies a
formula about its value, 'Data.CFTA.Symbol.valueName'. The analysis gives the
data of each e-class, the function gives its refinement, and the decision,
such as 'Data.CFTA.Refinement.Lattice.latticeImplies', decides the
implication. Each term of an e-class has the same value, so the analysis can
meet the refinements of the e-nodes of an e-class, as egglog merges the
lattice value of a function. An e-class without data, and an implication
that the decision does not know, do not satisfy the condition. For example,
the rule @x / x = 1@ with the condition that @x@ is not zero:

> refines latticeImplies refinementOf "x" (Atom Ne (Var (Name (Text.pack valueName))) (Lit 0))
-}
refines :: (Formula -> Formula -> Verdict) -> (d -> Formula) -> String -> Formula -> Condition s f d
refines implies refinementOf x goal = holds x (\d -> implies (refinementOf d) goal == Yes)

{- | How 'saturateWith' runs: its limits, an e-class analysis, and two
e-classes to make equal. Change 'defaultSaturation' with the fields:

> defaultSaturation {saturationAnalysis = Just constants, saturationGoal = Just (a, b)}
-}
data Saturation f d = Saturation
    { saturationLimits :: !Limits
    , saturationAnalysis :: !(Maybe (Analysis f d))
    {- ^ The data of each e-class is the fixed point of 'analyse', kept up to
    date after each iteration from the e-classes that changed, and each
    e-class with a leaf gets it, as hegg does in its rebuild.
    -}
    , saturationGoal :: !(Maybe (ClassId, ClassId))
    {- ^ Two e-classes: the saturation matches only the e-classes that they
    reach, and stops with 'Equal' when they are one e-class, as
    'saturateUntilEqual' does.
    -}
    }

-- | The limits of egg, no analysis, and no goal.
defaultSaturation :: Saturation f d
defaultSaturation = Saturation defaultLimits Nothing Nothing

{- | 'saturate' with the options of a 'Saturation' and a condition for each
rule. A condition sees the e-graph and the data of the analysis when its
match applies: as in egg, an added e-node gets its data from its children,
and a merge merges the data of its two e-classes. The data of the users of
an e-class follows after the iteration. An e-class whose data changes counts
as changed for the matching of only the changed e-classes, so a condition
that failed is tried again.
-}
saturateWith ::
    (Hashable s, Hashable f) =>
    Saturation f d -> [(Rule s f, Condition s f d)] -> EGraph s f -> (EGraph s f, Report)
saturateWith (Saturation limits analysis goal) rules = runWith analysis limits rules goal

-- | The roots of the e-classes.
eClasses :: EGraph s f -> [ClassId]
eClasses = map ClassId . IntMap.keys . classes

-- | The canonical e-nodes of an e-class: the symbol and the e-classes of the children of each.
eNodesOf :: EGraph s f -> ClassId -> [(f, [ClassId])]
eNodesOf g c = let ClassId i = find g c in [(f, cs) | ENode _ f cs <- canonicalNodes g i]

{- | Apply the rules to the e-classes that two e-classes reach, until the two
e-classes are one, nothing changes, or a limit stops it. This decides
whether the rules prove an equation within the limits, and its work does
not grow with the rest of the e-graph.
-}
saturateUntilEqual ::
    (Hashable s, Hashable f) => Limits -> [Rule s f] -> ClassId -> ClassId -> EGraph s f -> (EGraph s f, Report)
saturateUntilEqual limits rules a b = run limits rules (Just (a, b))

run ::
    (Hashable s, Hashable f) => Limits -> [Rule s f] -> Maybe (ClassId, ClassId) -> EGraph s f -> (EGraph s f, Report)
run limits rules = runWith (Nothing :: Maybe (Analysis f ())) limits [(r, mempty) | r <- rules]

runWith ::
    (Hashable s, Hashable f) =>
    Maybe (Analysis f d) ->
    Limits ->
    [(Rule s f, Condition s f d)] ->
    Maybe (ClassId, ClassId) ->
    EGraph s f ->
    (EGraph s f, Report)
runWith analysis limits rules goal g0 = go 0 IntMap.empty IntMap.empty IntMap.empty known0 g1
  where
    -- The changes before the saturation have older stamps than its first iteration.
    g1 = let h = rebuild g0 in h{clock = clock h + 1}
    known0 =
        maybe
            IntMap.empty
            (\a@Analysis{} -> fst (analyseFrom (analysisMake a) (analysisMerge a) g1 IntMap.empty (IntMap.keys (classes g1))))
            analysis
    -- After an iteration: update the data from the e-classes that changed,
    -- give each e-class with a leaf its leaf, and repeat until no leaf is
    -- new. An e-class whose data changed gets the stamp of the iteration. In
    -- the first iteration, each e-class of the start can need its leaf.
    -- Each round has its own tick of the clock, so a round analyses only the
    -- e-classes that changed after the round before it.
    settle first tick known h = case analysis of
        Nothing -> (h, known)
        Just a@Analysis{} ->
            let fresh = [j | (j, e) <- IntMap.toList (classes h), classStamp e >= tick]
                (known', changed) = analyseFrom (analysisMake a) (analysisMerge a) h known fresh
                stamped = h{classes = IntSet.foldr (IntMap.adjust (\e -> e{classStamp = tick})) (classes h) changed, clock = tick + 1}
                candidates = if first then IntMap.keys known' else IntSet.toList changed
                leaves =
                    [ (ClassId j, leaf)
                    | j <- candidates
                    , IntMap.member j (classes stamped)
                    , Just d <- [IntMap.lookup j known']
                    , Just leaf <- [analysisLeaf a d]
                    ]
                addLeaf (h', grew) (c, leaf) =
                    let (c', h'') = addNode (ENode (sortId h' c) leaf []) h'
                     in case union c c' h'' of
                            Just (u, h''') -> (h''', grew || u || added h'' /= added h')
                            Nothing -> (h'', grew || added h'' /= added h')
                (withLeaves, grew') = foldl' addLeaf (stamped, False) leaves
             in if grew' then settle False (tick + 1) known' (rebuild withLeaves) else (withLeaves, known')
    start = added g0
    size g = added g - start
    reached g = maybe False (uncurry (equivalent g)) goal
    -- ran: the clock at which each rule last ran; entered: the clock
    -- before the one at which each e-class entered the region of a goal, so
    -- that an e-class is new to a rule when it entered after the rule ran.
    go i bans ran entered known g
        | reached g = (g, Report i (size g) Equal)
        | i >= limitIterations limits = (g, Report i (size g) IterationLimit)
        | size g > limitNodes limits = (g, Report i (size g) NodeLimit)
        | otherwise =
            let region = case goal of
                    Nothing -> classes g
                    Just (a, b) -> reach g [a, b]
                now = clock g
                entered' = case goal of
                    Nothing -> entered
                    Just _ -> IntMap.union entered (IntMap.map (const (now - 1)) region)
                stampOf j = max (maybe 0 classStamp (IntMap.lookup j (classes g))) (IntMap.findWithDefault minBound j entered')
                -- The e-classes that changed since a clock, once for each clock.
                changedSets = Map.fromList [(t, IntSet.fromList [j | j <- IntMap.keys region, stampOf j >= t]) | t <- nubOrd (IntMap.elems ran)]
                changedSince t = Map.findWithDefault IntSet.empty t changedSets
                present = HashSet.fromList [f | e <- IntMap.elems region, FTA.Transition f _ _ <- classRow e]
                bySymbol = symbolIndex region
                dataIn h cur c = let ClassId j = find h c in IntMap.lookup j cur
                -- As egg does, the data of an e-node that an instance adds
                -- comes from its children when it is added, and a merge
                -- merges the data of its two e-classes, so that a condition
                -- sees them in the same iteration. The data of the users of
                -- an e-class follows after the iteration.
                madeIn h0 h cur = case analysis of
                    Just a@Analysis{} -> foldl' (makeOne a h) cur [added h0 .. added h - 1]
                    Nothing -> cur
                makeOne a h cur j = case nodesAt h j of
                    [ENode _ f cs]
                        | Just ds <- traverse (dataIn h cur) cs ->
                            IntMap.insert j (analysisMake a f ds) cur
                    _ -> cur
                mergedIn h h' c c' cur = case analysis of
                    Nothing -> cur
                    Just a@Analysis{} -> case (dataIn h cur c, dataIn h cur c') of
                        (Just x, Just y) -> IntMap.insert (root h' c) (analysisMerge a x y) cur
                        (Just x, Nothing) -> IntMap.insert (root h' c) x cur
                        (Nothing, Just y) -> IntMap.insert (root h' c) y cur
                        _ -> cur
                root h c = let ClassId j = find h c in j
                -- The ban of a rule, the rule if it ran, and its matches.
                search (k, (r, condition))
                    | not (all (`HashSet.member` present) (ruleSymbols r)) = (Nothing, Just k, [])
                    | Just (_, until', _) <- IntMap.lookup k bans, i < until' = (Nothing, Nothing, [])
                    | otherwise =
                        let since = IntMap.findWithDefault minBound k ran
                            ms = matchRule g region bySymbol stampOf since (if since == minBound then Nothing else Just (changedSince since)) r
                            (limit, _, ban) = IntMap.findWithDefault (limitMatches limits, 0, 5) k bans
                         in if limitMatches limits > 0 && length (take (limit + 1) ms) > limit
                                then (Just (k, (2 * limit, i + ban, 2 * ban)), Nothing, [])
                                else (Nothing, Just k, [(c, m, r, condition) | (c, m) <- ms])
                results = map search (zip [0 :: Int ..] rules)
                bans' = foldl' (\m (k, e) -> IntMap.insert k e m) bans [e | (Just e, _, _) <- results]
                ran' = foldl' (\m k -> IntMap.insert k now m) ran [k | (_, Just k, _) <- results]
                -- Stop as soon as a merge makes the two e-classes one, and
                -- when the e-nodes reach the limit.
                apply h _ changed [] = Right (h, changed)
                apply h _ changed _ | size h > limitNodes limits = Right (h, changed)
                apply h !cur changed ((c, m@(Subst vs _), r, condition) : rest)
                    | Condition check <- condition
                    , not (check h (dataIn h cur) (\v -> elemIndex v (ruleNames r) >>= (`IntMap.lookup` vs))) =
                        apply h cur changed rest
                    | otherwise = case instantiate m (sortId h c) (ruleRight r) h of
                        Nothing -> apply h cur changed rest
                        Just (c', h') ->
                            let !cur' = madeIn h h' cur
                             in case union c c' h' of
                                    Nothing -> apply h' cur' changed rest
                                    Just (u, h'') ->
                                        let !cur'' = if u then mergedIn h' h'' c c' cur' else cur'
                                         in if u && reached h'' then Left h'' else apply h'' cur'' (changed || u) rest
             in case apply g known False (concat [ms | (_, _, ms) <- results]) of
                    Left h ->
                        let (h', _) = settle (i == 0) now known (rebuild h)
                         in (h'{clock = clock h' + 1}, Report (i + 1) (size h') Equal)
                    Right (g', changed) ->
                        let (settled, known') = settle (i == 0) now known (rebuild g')
                            g'' = settled{clock = clock settled + 1}
                            banned = [until' | (_, until', _) <- IntMap.elems bans', until' > i + 1]
                            -- A banned rule can still apply, so an iteration that
                            -- changes nothing does not saturate while a ban lasts.
                            -- The bans move forward until the first one ends, as in
                            -- egg's BackoffScheduler.
                            shift = minimum banned - (i + 1)
                            moved = IntMap.map (\(l, u, b) -> if u > i + 1 then (l, u - shift, b) else (l, u, b)) bans'
                         in if not changed && size g'' == size g
                                then
                                    if null banned
                                        then (g'', Report (i + 1) (size g'') (if reached g'' then Equal else Saturated))
                                        else go (i + 1) moved ran' entered' known' g''
                                else go (i + 1) bans' ran' entered' known' g''
    sortId h c = let ClassId j = find h c in maybe 0 classSort (IntMap.lookup j (classes h))

-- The states of the e-graph automaton of 'ematchByIntersection'.
data GState = GRoot | GClass !Int | GName !Int | GSort !Int
    deriving (Eq, Ord)

-- The symbols of the e-graph automaton and of the product.
data GSymbol s f = GMatch | GNode !f !Int | GVar | GNameLeaf !Int | GSortNode !s !Int | GSortLeaf !Int | GNoSort
    deriving (Eq, Ord)

instance (Hashable s, Hashable f) => Hashable (GSymbol s f) where
    hashWithSalt salt = \case
        GMatch -> salt `hashWithSalt` (0 :: Int)
        GNode f n -> salt `hashWithSalt` (1 :: Int) `hashWithSalt` f `hashWithSalt` n
        GVar -> salt `hashWithSalt` (2 :: Int)
        GNameLeaf i -> salt `hashWithSalt` (3 :: Int) `hashWithSalt` i
        GSortNode s n -> salt `hashWithSalt` (4 :: Int) `hashWithSalt` s `hashWithSalt` n
        GSortLeaf k -> salt `hashWithSalt` (5 :: Int) `hashWithSalt` k
        GNoSort -> salt `hashWithSalt` (6 :: Int)

-- The symbols of the pattern automaton.
data PSymbol s f = PMatchRoot | PNodeSymbol !f !Int | PVariable | PAnyName | PSortSymbol !s !Int | PAnySort | PSortVariable
    deriving (Eq, Ord)

{- | The matches of a pattern by the definition: the terms of the product of
two automata, as 'FTA.intersectWith' builds it.

The e-graph automaton has a state for each e-class and for each sort. An
e-node @f(c1, ..., cn)@ of sort @k@ in the e-class @c@ is the transition
@f(k, c1, ..., cn) -> c@: the sort is the first child, as in the encoding
of types in an ECTA. A further transition of @c@ names the e-class and its
sort, for the variables. The automaton of the pattern accepts the instances
of the pattern. A variable that occurs twice, and a sort variable that
occurs twice, are equality classes of paths: an equality constraint, as in
an ECTA. A term of the product that satisfies the constraint is a match.

This is slow, because it builds the product and lists its terms. 'ematch'
gives the same matches. A node with two sort patterns keeps the inner one
here; 'ematch' requires both.
-}
ematchByIntersection ::
    (Ord s, Hashable s, Ord f, Hashable f) => EGraph s f -> Pattern s f -> [(ClassId, Map.Map String ClassId)]
ematchByIntersection g pat = case (FTA.mkFTA GRoot graphRows, FTA.mkFTA (-1 :: Int) patternRows) of
    (Right graph, Right patterns) -> case FTA.intersectWith same (\_ c -> c) graph patterns of
        Right product' ->
            [ (c, bindings)
            | term@(Node GMatch [instance']) <- FTA.terms product'
            , all (\t -> equalitiesHold (FTA.transitionConstraint t) term) (FTA.transitionsFrom product' (FTA.initialState product'))
            , Just c <- [classOf instance']
            , Just bindings <- [bind pat instance' Map.empty]
            ]
        Left _ -> []
    _ -> []
  where
    nodesOf = IntMap.mapWithKey (\i _ -> canonicalNodes g i) (classes g)
    graphRows =
        (GRoot, [FTA.Transition GMatch [GClass i] noConstraint | i <- IntMap.keys nodesOf])
            : [ ( GClass i
                , FTA.Transition GVar [GName i, GSort (classSort e)] noConstraint
                    : [ FTA.Transition (GNode f (length cs)) (GSort k : [GClass j | ClassId j <- cs]) noConstraint
                      | ENode k f cs <- nodesOf IntMap.! i
                      ]
                )
              | (i, e) <- IntMap.toList (classes g)
              ]
            ++ [(GName i, [FTA.Transition (GNameLeaf i) [] noConstraint]) | i <- IntMap.keys nodesOf]
            ++ (GSort 0, [FTA.Transition GNoSort [] noConstraint])
            : [ ( GSort k
                , [FTA.Transition (GSortNode s (length ks)) (map GSort ks) noConstraint, FTA.Transition (GSortLeaf k) [] noConstraint]
                )
              | (k, SortNode s ks) <- IntMap.toList (sortNodes g)
              ]
    -- The pattern automaton: -1 is the root, -2 a name, -3 any sort, -4 a
    -- sort variable, and 0, 1, ... the other states.
    patternRows =
        let (top, rows, _, occ) = goPattern Nothing pat [0] 0
            classes' = [map (path . map ChildIndex) ps | ps <- Map.elems occ, length ps > 1]
            constraint = if null classes' then noConstraint else equalityConstraint (mkEqConstraints classes')
         in (-1, [FTA.Transition PMatchRoot [top] constraint])
                : (-2, [FTA.Transition PAnyName [] noConstraint])
                : (-3, [FTA.Transition PAnySort [] noConstraint])
                : (-4, [FTA.Transition PSortVariable [] noConstraint])
                : rows
    goPattern _ (PSorted sp p) here next = goPattern (Just sp) p here next
    goPattern sort (PVar v) here next =
        let (sortState, rows, next', occ) = goSort sort (here ++ [1]) (next + 1)
         in ( next
            , (next, [FTA.Transition PVariable [-2, sortState] noConstraint]) : rows
            , next'
            , Map.insertWith (++) (Left v) [here ++ [0]] occ
            )
    goPattern sort (PNode f ps) here next =
        let (sortState, rows, next1, occ) = goSort sort (here ++ [0]) (next + 1)
            (kids, rows', next', occ') =
                foldl'
                    ( \(ks, rs, n, o) (i, p) -> let (k, r, n', o') = goPattern Nothing p (here ++ [i]) n in (ks ++ [k], rs ++ r, n', Map.unionWith (++) o o')
                    )
                    ([], rows, next1, occ)
                    (zip [1 ..] ps)
         in (next, (next, [FTA.Transition (PNodeSymbol f (length ps)) (sortState : kids) noConstraint]) : rows', next', occ')
    goSort Nothing _ next = (-3, [], next, Map.empty)
    goSort (Just (SVar a)) here next = (-4, [], next, Map.singleton (Right a) [here])
    goSort (Just (SNode s ps)) here next =
        let (kids, rows, next', occ) =
                foldl'
                    ( \(ks, rs, n, o) (i, p) -> let (k, r, n', o') = goSort (Just p) (here ++ [i]) n in (ks ++ [k], rs ++ r, n', Map.unionWith (++) o o')
                    )
                    ([], [], next + 1, Map.empty)
                    (zip [0 ..] ps)
         in (next, (next, [FTA.Transition (PSortSymbol s (length ps)) kids noConstraint]) : rows, next', occ)
    same GMatch PMatchRoot = Just GMatch
    same (GNode f n) (PNodeSymbol f' n') | f == f' && n == n' = Just (GNode f n)
    same GVar PVariable = Just GVar
    same (GNameLeaf i) PAnyName = Just (GNameLeaf i)
    same (GSortNode s n) (PSortSymbol s' n') | s == s' && n == n' = Just (GSortNode s n)
    same (GSortLeaf k) PAnySort = Just (GSortLeaf k)
    same GNoSort PAnySort = Just GNoSort
    same (GSortLeaf k) PSortVariable = Just (GSortLeaf k)
    same _ _ = Nothing
    -- The e-class of an instance, through the memo.
    classOf (Node GVar [Node (GNameLeaf i) [], _]) = Just (find g (ClassId i))
    classOf (Node (GNode f _) (sortChild : kids)) = do
        k <- sortIdOf sortChild
        cs <- traverse classOf kids
        find g <$> HashMap.lookup (ENode k f cs) (memo g)
    classOf _ = Nothing
    sortIdOf (Node GNoSort []) = Just 0
    sortIdOf (Node (GSortLeaf k) []) = Just k
    sortIdOf (Node (GSortNode s _) kids) = traverse sortIdOf kids >>= \ks -> HashMap.lookup (SortNode s ks) (sortIds g)
    sortIdOf _ = Nothing
    bind (PSorted _ p) t b = bind p t b
    bind (PVar v) (Node GVar [Node (GNameLeaf i) [], _]) b = Just (Map.insert v (find g (ClassId i)) b)
    bind (PNode _ ps) (Node (GNode _ _) (_ : kids)) b = foldM (\acc (p, t) -> bind p t acc) b (zip ps kids)
    bind _ _ _ = Nothing
