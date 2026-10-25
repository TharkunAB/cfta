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

= E-graphs are tree automata

An e-graph is a bottom-up deterministic tree automaton (Pollock and Haan, in
Wang et al., "E-Graphs, VSAs, and Tree Automata: a Rosetta Stone", EGRAPHS
2022):

* An e-class is a state.
* An e-node @f(c1, ..., cn)@ of the e-class @c@ is a transition
  @f(c1, ..., cn) -> c@.
* The hash-cons makes the automaton deterministic: one left side of a
  transition has one state.
* Rebuilding keeps the automaton deterministic after a merge: when two
  transitions become the same, their states merge. This is the congruence.

So the terms of an e-class are the language of its state. 'classAutomaton'
gives this automaton, and "Data.CFTA.Sized" in @cfta-generator@ counts,
lists, ranks, unranks, and samples the terms. A general FTA has no
hash-cons: two transitions with one left side can have two states. A
version space algebra is an acyclic FTA.

An ECTA (Koppel et al., ICFP 2022) adds equality constraints to the
transitions of an FTA: the subterms at some paths must be equal. With
equality constraints, an automaton describes some sets of terms with far
fewer states, and some infinite sets that no FTA describes, such as the
terms @f(t, t)@. Equality constraints occur here in two places:

* A pattern in which a variable occurs twice, such as @x + x@, accepts the
  terms whose subterms at the two paths of @x@ are equal.
* An ECTA of typed terms puts the type of a term in a child, and equality
  constraints make the types agree. A sorted e-graph keeps the sort in the
  e-node instead. A sort variable that occurs twice in a pattern is an
  equality constraint between the paths of the sorts.

= E-matching is an intersection

The matches of a pattern are the terms of the product of the e-graph
automaton and the automaton of the pattern that satisfy the equality
constraints of the pattern. 'ematchByIntersection' computes the matches by
this definition, with 'FTA.intersectWith'. 'ematch' and the saturation
explore the same product from a few roots, one run at a time, and check the
equality constraints as they bind the variables. The test suite checks that
the two give the same matches.
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

    -- * Patterns and rules
    Pattern (..),
    SortPattern (..),
    Rule,
    RuleError (..),
    rule,
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
) where

import Control.Monad (foldM)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.List (minimumBy, sortOn, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Ord (comparing)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalitiesHold, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (ChildIndex (..), path)
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

{- | A pattern: a variable, a symbol with the patterns of its children, or a
pattern whose e-class has a sort. A variable that occurs twice matches one
e-class at both places.
-}
data Pattern s f
    = PVar !String
    | PNode !f ![Pattern s f]
    | PSorted !(SortPattern s) !(Pattern s f)
    deriving (Eq, Show)

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
    pure (Rule l r symbols (anchorsOf l) (map fst (sortOn snd (Map.toList vars))))

{- | The rules of an equation: the direction from each side whose other side
has no other variables.
-}
equation :: (Hashable f) => Pattern s f -> Pattern s f -> [Rule s f]
equation a b = [r | Right r <- [rule a b, rule b a]]

patternSymbols :: Pattern s f -> [f]
patternSymbols (PVar _) = []
patternSymbols (PNode f ps) = f : concatMap patternSymbols ps
patternSymbols (PSorted _ p) = patternSymbols p

anchorsOf :: CPat s f -> [(f, [(f, Int, Int)])]
anchorsOf = go []
  where
    go _ (CVar _ _) = []
    go above (CNode f kids _) = (f, reverse above) : concat [go ((f, length kids, k) : above) kid | (k, kid) <- zip [0 ..] kids]

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
    Just (SortNode s' ks) | s == s' && length ks == length ps -> foldM (\acc (p, k') -> matchSort g p k' acc) b (zip ps ks)
    _ -> Nothing

-- | The canonical e-nodes of the e-classes that some e-classes reach through their children.
reach :: (Hashable f) => EGraph s f -> [ClassId] -> IntMap.IntMap [ENode f]
reach g = go IntMap.empty
  where
    go seen [] = seen
    go seen (c0 : rest)
        | IntMap.member i seen = go seen rest
        | otherwise = go (IntMap.insert i ns seen) (concat [cs | ENode _ _ cs <- ns] ++ rest)
      where
        ClassId i = find g c0
        ns = canonicalNodes g i

canonicalNodes :: (Hashable f) => EGraph s f -> Int -> [ENode f]
canonicalNodes g i = maybe [] (HashSet.toList . HashSet.map (canon g) . classNodes) (IntMap.lookup i (classes g))

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
    EGraph s f -> IntMap.IntMap [ENode f] -> HashMap.HashMap f (Int, [ClassId]) -> Rule s f -> [(ClassId, Subst)]
matchRule g region bySymbol r = [(c, m) | c <- roots, m <- down (ruleLeft r) c (Subst IntMap.empty IntMap.empty)]
  where
    down (CVar v sorts) c (Subst vs ss) = case sortsFrom c sorts ss of
        Nothing -> []
        Just ss' -> case IntMap.lookup v vs of
            Nothing -> [Subst (IntMap.insert v c vs) ss']
            Just c' | equivalent g c c' -> [Subst vs ss']
            _ -> []
    down (CNode f kids sorts) c@(ClassId i) (Subst vs ss) = case sortsFrom c sorts ss of
        Nothing -> []
        Just ss' ->
            [ m
            | ENode _ f' cs <- IntMap.findWithDefault [] i region
            , f' == f
            , length cs == length kids
            , m <- foldM (\acc (child, kid) -> down kid child acc) (Subst vs ss') (zip cs kids)
            ]
    sortsFrom (ClassId i) sorts ss = do
        e <- IntMap.lookup i (classes g)
        foldM (\b sp -> matchSort g sp (classSort e) b) ss sorts
    roots = case ruleAnchors r of
        [] -> map ClassId (IntMap.keys region)
        anchors ->
            let (f, steps) = minimumBy (comparing (\(h, _) -> maybe 0 fst (HashMap.lookup h bySymbol))) anchors
                start = IntSet.fromList [i | ClassId i <- maybe [] snd (HashMap.lookup f bySymbol)]
             in map ClassId (IntSet.toAscList (foldr up start steps))
    -- The e-classes with an e-node of the step whose child is in the set.
    up (f, n, k) xs =
        IntSet.fromList
            [ j
            | i <- IntSet.toList xs
            , Just e <- [IntMap.lookup i (classes g)]
            , (ENode _ f' cs, owner) <- classUsers e
            , f' == f
            , length cs == n
            , Just child <- [cs !? k]
            , find g child == ClassId i
            , let ClassId j = find g owner
            , IntMap.member j region
            ]

-- | The number of e-classes with each symbol in a region, and the e-classes in ascending order.
symbolIndex :: (Hashable f) => IntMap.IntMap [ENode f] -> HashMap.HashMap f (Int, [ClassId])
symbolIndex region =
    HashMap.map (\cs -> (length cs, cs)) $
        HashMap.fromListWith
            (flip (++))
            [(f, [ClassId i]) | (i, ns) <- IntMap.toList region, f <- HashSet.toList (HashSet.fromList [f' | ENode _ f' _ <- ns])]

{- | The matches of a pattern: the e-class of each instance, and the e-class
of each variable.
-}
ematch :: (Eq s, Hashable f) => EGraph s f -> Pattern s f -> [(ClassId, Map.Map String ClassId)]
ematch g p = case rule p p of
    Left _ -> []
    Right r ->
        let region = IntMap.mapWithKey (\i _ -> canonicalNodes g i) (classes g)
         in [ (c, Map.fromList [(v, vs IntMap.! i) | (i, v) <- zip [0 ..] (ruleNames r)])
            | (c, Subst vs _) <- matchRule g region (symbolIndex region) r
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
run limits rules goal g0 = go 0 IntMap.empty (rebuild g0)
  where
    start = added g0
    size g = added g - start
    reached g = maybe False (uncurry (equivalent g)) goal
    go i bans g
        | reached g = (g, Report i (size g) Equal)
        | i >= limitIterations limits = (g, Report i (size g) IterationLimit)
        | size g > limitNodes limits = (g, Report i (size g) NodeLimit)
        | otherwise =
            let region = case goal of
                    Nothing -> IntMap.mapWithKey (\j _ -> canonicalNodes g j) (classes g)
                    Just (a, b) -> reach g [a, b]
                present = HashSet.fromList [f | ns <- IntMap.elems region, ENode _ f _ <- ns]
                bySymbol = symbolIndex region
                search (k, r)
                    | not (all (`HashSet.member` present) (ruleSymbols r)) = (Nothing, [])
                    | Just (_, until', _) <- IntMap.lookup k bans, i < until' = (Nothing, [])
                    | otherwise =
                        let ms = matchRule g region bySymbol r
                            (limit, _, ban) = IntMap.findWithDefault (limitMatches limits, 0, 5) k bans
                         in if limitMatches limits > 0 && length (take (limit + 1) ms) > limit
                                then (Just (k, (2 * limit, i + ban, 2 * ban)), [])
                                else (Nothing, [(c, m, r) | (c, m) <- ms])
                results = map search (zip [0 :: Int ..] rules)
                bans' = foldl' (\m (k, e) -> IntMap.insert k e m) bans [e | (Just e, _) <- results]
                -- Stop as soon as a merge makes the two e-classes one, and
                -- when the e-nodes reach the limit.
                apply h changed [] = Right (h, changed)
                apply h changed _ | size h > limitNodes limits = Right (h, changed)
                apply h changed ((c, m, r) : rest) =
                    case instantiate m (sortId h c) (ruleRight r) h of
                        Nothing -> apply h changed rest
                        Just (c', h') -> case union c c' h' of
                            Nothing -> apply h' changed rest
                            Just (u, h'') -> if u && reached h'' then Left h'' else apply h'' (changed || u) rest
             in case apply g False (concatMap snd results) of
                    Left h -> let h' = rebuild h in (h', Report (i + 1) (size h') Equal)
                    Right (g', changed) ->
                        let g'' = rebuild g'
                         in if not changed && size g'' == size g
                                then (g'', Report (i + 1) (size g'') (if reached g'' then Equal else Saturated))
                                else go (i + 1) bans' g''
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
