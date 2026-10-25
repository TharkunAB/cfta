{-# LANGUAGE PatternSynonyms #-}

{- | E-graphs with sorts.

An e-graph holds a set of terms and an equivalence of these terms that is a
congruence: when two terms are equal, the terms that differ only in them
are equal too. An e-class is a set of equal terms. An e-node is a symbol
with an e-class for each child. Each e-node has one e-class, and two e-nodes
with the same symbol and children are the same e-node (the hash-cons).

Each e-class has a sort, or no sort. A sort is a term over sort symbols,
such as a type. The sort is part of the identity of an e-node, so the
constant @[]@ of sort @[Int]@ and the constant @[]@ of sort @[Bool]@ are two
e-nodes. Two e-classes of different sorts do not merge. Sorts are
hash-consed as well, and they never merge.

The e-graph is a persistent value. 'classAutomaton' gives the terms of one
e-class as an automaton, so "Data.CFTA.Sized" in @cfta-generator@ counts,
lists, ranks, and unranks them.
-}
module Data.CFTA.EGraph (
    -- * E-graphs
    EGraph,
    ClassId,
    emptyEGraph,
    addTerm,
    addTermWith,
    find,
    equivalent,
    merge,
    sortOf,
    eClassCount,
    eNodeCount,

    -- * The terms of an e-class
    classAutomaton,
    classAutomatonWith,
) where

import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Term (Term, pattern Node)

-- | The identity of an e-class. 'find' gives the identity of the root of its e-class.
newtype ClassId = ClassId Int
    deriving (Eq, Ord, Show, Hashable)

-- | A sort: its symbol and the identities of its children. The identity 0 is no sort.
data SortNode s = SortNode !s ![Int]
    deriving (Eq)

instance (Hashable s) => Hashable (SortNode s) where
    hashWithSalt salt (SortNode s ks) = salt `hashWithSalt` s `hashWithSalt` ks

-- | An e-node: the identity of its sort, its symbol, and the e-classes of its children.
data ENode f = ENode !Int !f ![ClassId]
    deriving (Eq)

instance (Hashable f) => Hashable (ENode f) where
    hashWithSalt salt (ENode k f cs) = salt `hashWithSalt` k `hashWithSalt` f `hashWithSalt` cs

{- | An e-class. Its e-nodes can have children that are not roots; 'canon'
replaces them. Its users are the e-nodes that have the e-class as a child,
with their e-classes.
-}
data EClass f = EClass
    { classNodes :: !(HashSet.HashSet (ENode f))
    , classUsers :: ![(ENode f, ClassId)]
    , classUserCount :: !Int
    , classSort :: !Int
    }

{- | An e-graph of terms over the symbols @f@, with sorts over the sort
symbols @s@.
-}
data EGraph s f = EGraph
    { parents :: !(IntMap.IntMap ClassId)
    -- ^ The parent of each e-class that is not a root.
    , classes :: !(IntMap.IntMap (EClass f))
    -- ^ The roots.
    , memo :: !(HashMap.HashMap (ENode f) ClassId)
    -- ^ The canonical e-nodes, after 'rebuild'.
    , nodeCount :: !Int
    -- ^ The size of 'memo'. 'HashMap.size' walks the map.
    , classCount :: !Int
    -- ^ The size of 'classes'. 'IntMap.size' walks the map.
    , added :: !Int
    -- ^ The e-nodes that 'addNode' made. Each one gets a new e-class.
    , sortIds :: !(HashMap.HashMap (SortNode s) Int)
    , sortNodes :: !(IntMap.IntMap (SortNode s))
    , pending :: ![ClassId]
    -- ^ The roots whose users 'rebuild' must make canonical.
    }

-- | The e-graph without terms.
emptyEGraph :: EGraph s f
emptyEGraph = EGraph IntMap.empty IntMap.empty HashMap.empty 0 0 0 HashMap.empty IntMap.empty []

-- | The root of the e-class of an identity.
find :: EGraph s f -> ClassId -> ClassId
find g c@(ClassId i) = case IntMap.lookup i (parents g) of
    Just p -> find g p
    Nothing -> c

-- | Whether two identities are in one e-class.
equivalent :: EGraph s f -> ClassId -> ClassId -> Bool
equivalent g a b = find g a == find g b

canon :: EGraph s f -> ENode f -> ENode f
canon g (ENode k f cs) = ENode k f (map (find g) cs)

lookupClass :: EGraph s f -> ClassId -> Maybe (EClass f)
lookupClass g c = let ClassId i = find g c in IntMap.lookup i (classes g)

-- | The identity of a sort.
internSort :: (Hashable s) => Term s -> EGraph s f -> (Int, EGraph s f)
internSort (Node s ts) g0 =
    let (ks, g1) = foldr (\t (acc, h) -> let (k, h') = internSort t h in (k : acc, h')) ([], g0) ts
        n = SortNode s ks
     in case HashMap.lookup n (sortIds g1) of
            Just k -> (k, g1)
            Nothing ->
                let k = maybe 1 ((+ 1) . fst) (IntMap.lookupMax (sortNodes g1))
                 in (k, g1{sortIds = HashMap.insert n k (sortIds g1), sortNodes = IntMap.insert k n (sortNodes g1)})

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
    Just c -> (find g c, g)
    Nothing ->
        let c@(ClassId i) = ClassId (added g)
            ENode k _ cs = n
            use = IntMap.adjust (\e -> e{classUsers = (n, c) : classUsers e, classUserCount = classUserCount e + 1})
         in ( c
            , g
                { classes = foldr (\(ClassId j) -> use j) (IntMap.insert i (EClass (HashSet.singleton n) [] 0 k) (classes g)) cs
                , memo = HashMap.insert n c (memo g)
                , nodeCount = nodeCount g + 1
                , classCount = classCount g + 1
                , added = added g + 1
                }
            )
  where
    n = canon g n0

-- | Add a term without sorts, and give its e-class.
addTerm :: (Hashable f) => Term f -> EGraph s f -> (ClassId, EGraph s f)
addTerm (Node f ts) g0 =
    let (cs, g1) = foldr (\t (acc, h) -> let (c, h') = addTerm t h in (c : acc, h')) ([], g0) ts
     in addNode (ENode 0 f cs) g1

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
union :: (Hashable f) => ClassId -> ClassId -> EGraph s f -> Maybe (Bool, EGraph s f)
union a b g
    | ra == rb = Just (False, g)
    | otherwise = case (IntMap.lookup ia (classes g), IntMap.lookup ib (classes g)) of
        (Just ea, Just eb)
            | classSort ea /= classSort eb -> Nothing
            | otherwise ->
                let (big, small, eBig, eSmall) =
                        if classUserCount ea >= classUserCount eb then (ra, rb, ea, eb) else (rb, ra, eb, ea)
                    ClassId iBig = big
                    ClassId iSmall = small
                    joined =
                        EClass
                            (HashSet.union (classNodes eSmall) (classNodes eBig))
                            (classUsers eSmall ++ classUsers eBig)
                            (classUserCount eSmall + classUserCount eBig)
                            (classSort eBig)
                 in Just
                        ( True
                        , g
                            { parents = IntMap.insert iSmall big (parents g)
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
rebuild g0 = case pending g0 of
    [] -> g0
    todo ->
        rebuild (foldl' repair g0{pending = []} (IntSet.toList (IntSet.fromList [i | c <- todo, let ClassId i = find g0 c])))
  where
    repair g i = case IntMap.lookup i' (classes g) of
        Nothing -> g
        Just e ->
            let users = classUsers e
                -- Take the users out of the e-class and the memo, then add
                -- them again in canonical form. A merge in 'step' can join
                -- this e-class to another one, so the users of the other one
                -- stay in the joined e-class.
                (m1, n1) =
                    foldl'
                        (\(m, n) (u, _) -> if HashMap.member u m then (HashMap.delete u m, n - 1) else (m, n))
                        (memo g, nodeCount g)
                        users
                g1 = g{memo = m1, nodeCount = n1, classes = IntMap.insert i' e{classUsers = [], classUserCount = 0} (classes g)}
                (g2, seen) = foldl' step (g1, HashMap.empty) users
                step (h, s) (u, owner) =
                    let u' = canon h u
                        h1 = case HashMap.lookup u' (memo h) of
                            Just other -> maybe h snd (union owner other h)
                            Nothing -> h{memo = HashMap.insert u' (find h owner) (memo h), nodeCount = nodeCount h + 1}
                     in (h1, HashMap.insert u' (find h1 owner) s)
                ClassId root = find g2 (ClassId i')
                users' = HashMap.toList seen
             in g2
                    { classes =
                        IntMap.adjust
                            (\e' -> e'{classUsers = users' ++ classUsers e', classUserCount = length users' + classUserCount e'})
                            root
                            (classes g2)
                    }
      where
        ClassId i' = find g (ClassId i)

-- | The number of e-classes.
eClassCount :: EGraph s f -> Int
eClassCount = classCount

-- | The number of e-nodes.
eNodeCount :: EGraph s f -> Int
eNodeCount = nodeCount

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
    go _ [] = []
    go seen (c@(ClassId i) : rest)
        | IntSet.member i seen = go seen rest
        | otherwise =
            let nodes = maybe [] (map (canon g) . HashSet.toList . classNodes) (IntMap.lookup i (classes g))
                row = [FTA.Transition (label (sortTerm g k) f) cs noConstraint | ENode k f cs <- nodes]
             in (c, row) : go (IntSet.insert i seen) (concat [cs | ENode _ _ cs <- nodes] ++ rest)
