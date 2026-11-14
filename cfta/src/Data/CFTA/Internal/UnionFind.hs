{- | Lightweight union-find implementation suitable for nondeterministic search.

Mutable union-find, as in @Data.Equivalence.Monad@, can be faster overall,
but enumeration branches in the list monad need a structure that can be copied
and backtracked cheaply. This module stores parent pointers in an 'IntMap' and
returns updated structures from 'union'. It is the linked-list
representation of disjoint sets with the weighted-union heuristic (Cormen et
al., Introduction to Algorithms): the representative of a set holds the size
and the members of the set, and a union points each member of the smaller
set at the representative of the larger set. So the parent of a variable is
always its representative, 'root' takes one lookup, and n unions point
O(n log n) members in all.

In a constrained enumeration of 20,000 terms of the typed-expression ECTA,
'find' takes 1.7% of the instructions, and all operations of @containers@
together take 5.5%. So a mutable union-find with an undo log could save at
most about 7%, which does not pay for the backtracking that it needs.
-}
module Data.CFTA.Internal.UnionFind (
    UVarGen,
    initUVarGen,
    nextUVar,
    UVar,
    uvarToInt,
    intToUVar,
    UnionFind,
    withInitialValues,
    union,
    unionRoots,
    find,
    root,
) where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

----------------------------------------------------------

---------------------------
-------- UVarGen
---------------------------

-- | Fresh supply for enumeration variables.
newtype UVarGen = UVarGen Int
    deriving (Eq, Ord, Show)

-- | Initial variable supply.
initUVarGen :: UVarGen
initUVarGen = UVarGen 0

-- | Allocate one fresh variable and advance the supply.
nextUVar :: UVarGen -> (UVarGen, UVar)
nextUVar (UVarGen n) = (UVarGen (n + 1), UVar n)

---------------------------
-------- UVar
---------------------------

-- | Union-find variable identifier.
newtype UVar = UVar Int
    deriving (Eq, Ord, Show)

-- | Convert a variable to its dense integer id.
uvarToInt :: UVar -> Int
uvarToInt (UVar i) = i

-- | Reconstruct a variable from its dense integer id.
intToUVar :: Int -> UVar
intToUVar = UVar

---------------------------
-------- Union-find data structure
---------------------------

{- | What the forest stores for one variable.

A 'Parent' points to the representative of the set of the variable. A
'Root' is the representative of its set and holds the size of the set and
the set: the integer ids of its members, the representative too. 'IntSet.size'
walks the set, so the size is a field.
-}
data Entry = Parent !UVar | Root !Int !IntSet
    deriving (Eq, Ord, Show)

-- | Persistent union-find forest, keyed by the integer id of a variable.
data UnionFind = UnionFind {getUnionFindMap :: !(IntMap Entry)}
    deriving (Eq, Ord, Show)

-- | Forest containing each supplied variable as a singleton set.
withInitialValues :: [UVar] -> UnionFind
withInitialValues uvs = UnionFind $ IntMap.fromList [(i, Root 1 (IntSet.singleton i)) | i <- map uvarToInt uvs]

---------------------------
-------- Union-find operations
---------------------------

-- | Merge the two variable classes, preferring the larger class as root.
union :: UVar -> UVar -> UnionFind -> UnionFind
union uv1 uv2 uf
    | r1 == r2 = uf
    | otherwise = snd (unionRoots r1 r2 uf)
  where
    r1 = root uv1 uf
    r2 = root uv2 uf

{- | Merge the classes of two different representatives, and give the
representative of the merged class: the representative of the larger class.
-}
unionRoots :: UVar -> UVar -> UnionFind -> (UVar, UnionFind)
unionRoots r1 r2 (UnionFind m) =
    let (big, bigSize, bigSet, smallSize, smallSet) =
            if s1 < s2 then (r2, s2, set2, s1, set1) else (r1, s1, set1, s2, set2)
        -- Each member of the smaller set now points at the new representative.
        pointed = IntSet.foldl' (\acc v -> IntMap.insert v (Parent big) acc) m smallSet
     in ( big
        , UnionFind (IntMap.insert (uvarToInt big) (Root (bigSize + smallSize) (IntSet.union smallSet bigSet)) pointed)
        )
  where
    (s1, set1) = entryOf r1
    (s2, set2) = entryOf r2
    -- A variable without an entry is the representative of its own set.
    entryOf r = case IntMap.lookup (uvarToInt r) m of
        Just (Root size set) -> (size, set)
        _ -> (1, IntSet.singleton (uvarToInt r))

-- | Find a variable's representative. The forest stays the same.
find :: UVar -> UnionFind -> (UVar, UnionFind)
find uv uf = (root uv uf, uf)

-- | The representative of a variable: its parent, or the variable itself when it has none.
root :: UVar -> UnionFind -> UVar
root uv (UnionFind m) = case IntMap.lookup (uvarToInt uv) m of
    Just (Parent p) -> p
    _ -> uv

---------------------------
-------- LiquidHaskell specifications
---------------------------

-- The specifications are after the code. A specification above a definition
-- moves the source locations that GHC writes into the object file.

-- LiquidHaskell does not check the contracts of initUVarGen, uvarToInt and
-- intToUVar. The result of each function is a newtype cast, and the plugin
-- gives a cast the refinement of the expected type. So these three contracts
-- are assumptions. Each one says that the cast keeps the number. The bounds on
-- the keys and the members below depend on the contract of uvarToInt.
{-@ initUVarGen :: {v:UVarGen | v == 0} @-}

{-@ nextUVar :: g:UVarGen -> ({v:UVarGen | v == g + 1}, {v:UVar | v == g}) @-}

{-@ uvarToInt :: u:UVar -> {v:Int | v == u} @-}

{-@ intToUVar :: i:Int -> {v:UVar | v == i} @-}

-- The number of members of a Root is at most its size. The bound is not an
-- equality, because the specification of IntSet.union does not say that the
-- two sets are disjoint.
-- The abstract refinement p is a condition on the parent of each Parent, and
-- q is a condition on the members of each Root. The caller chooses p and q,
-- for example "the id is less than n" and "intSetMax is less than n".
{-@ data Entry <p :: UVar -> Bool, q :: IntSet -> Bool>
      = Parent {entryParent :: UVar<p>}
      | Root {entrySize :: {v:Int | 0 < v}, entryMembers :: {s:IntSet<q> | intSetSize s <= entrySize}}
@-}

-- All entries of a forest have the same p and q. The abstract refinement k is
-- a condition on the map, for example "intMapKeyMax is less than n".
{-@ data UnionFind <p :: UVar -> Bool, q :: IntSet -> Bool, k :: IntMap Entry -> Bool> = UnionFind {getUnionFindMap :: IntMap (Entry<p, q>) <<k>>} @-}

-- The refinement constraints below link the conditions. The abstract
-- refinement r is a condition on one id. For the conditions of the example,
-- with r "the id is less than n", each constraint is true:
-- 1. A variable with p has r as an Int.
-- 2. The set of one id with r has q.
-- 3. The union of two sets with q has q.
-- 4. An id that is at most intSetMax of a set with q has r.
-- 5. A map with k keeps k after the insertion of a key with r.
-- 6. A map whose largest key has r has k.
-- 7. A map whose largest key is minBound has k. The number in the constraint
--    is minBound of a 64-bit Int, the value of intMapKeyMax for the empty
--    map. The parser does not accept a constraint without a binder, so this
--    constraint binds d and does not use it.

-- The variables become keys and members, so each variable must have p.
{-@ withInitialValues
      :: forall <p :: UVar -> Bool, q :: IntSet -> Bool, r :: Int -> Bool, k :: IntMap Entry -> Bool>.
         {u :: UVar<p> |- {v:Int | v == u} <: Int<r>}
         {x :: Int<r> |- {v:IntSet | intSetMax v == x} <: IntSet<q>}
         {x :: Int<r> |- {v:IntMap (Entry<p, q>) | intMapKeyMax v == x} <: IntMap (Entry<p, q>) <<k>>}
         {d :: Int |- {v:IntMap (Entry<p, q>) | intMapKeyMax v == -9223372036854775808} <: IntMap (Entry<p, q>) <<k>>}
         [UVar<p>] -> UnionFind<p, q, k>
@-}

{-@ union
      :: forall <p :: UVar -> Bool, q :: IntSet -> Bool, r :: Int -> Bool, k :: IntMap Entry -> Bool>.
         {u :: UVar<p> |- {v:Int | v == u} <: Int<r>}
         {x :: Int<r> |- {v:IntSet | intSetMax v == x} <: IntSet<q>}
         {a :: IntSet<q>, b :: IntSet<q> |- {v:IntSet | intSetMax v <= intSetMax a || intSetMax v <= intSetMax b} <: IntSet<q>}
         {s :: IntSet<q>, x :: {x:Int | x <= intSetMax s} |- {v:Int | v == x} <: Int<r>}
         {m :: IntMap (Entry<p, q>) <<k>>, x :: Int<r> |- {v:IntMap (Entry<p, q>) | intMapKeyMax v <= intMapKeyMax m || intMapKeyMax v <= x} <: IntMap (Entry<p, q>) <<k>>}
         UVar<p> -> UVar<p> -> UnionFind<p, q, k> -> UnionFind<p, q, k>
@-}

-- An inference hint for the result of unionRoots. LiquidHaskell checks the
-- result with this qualifier. The qualifier is not an assumption.
{-@ qualif OneOf(v:a, x:a, y:a) { v == x || v == y } @-}

-- The new representative is one of the two old representatives.
{-@ unionRoots
      :: forall <p :: UVar -> Bool, q :: IntSet -> Bool, r :: Int -> Bool, k :: IntMap Entry -> Bool>.
         {u :: UVar<p> |- {v:Int | v == u} <: Int<r>}
         {x :: Int<r> |- {v:IntSet | intSetMax v == x} <: IntSet<q>}
         {a :: IntSet<q>, b :: IntSet<q> |- {v:IntSet | intSetMax v <= intSetMax a || intSetMax v <= intSetMax b} <: IntSet<q>}
         {s :: IntSet<q>, x :: {x:Int | x <= intSetMax s} |- {v:Int | v == x} <: Int<r>}
         {m :: IntMap (Entry<p, q>) <<k>>, x :: Int<r> |- {v:IntMap (Entry<p, q>) | intMapKeyMax v <= intMapKeyMax m || intMapKeyMax v <= x} <: IntMap (Entry<p, q>) <<k>>}
         r1:UVar<p> -> r2:UVar<p> -> UnionFind<p, q, k> -> ({v:UVar<p> | v == r1 || v == r2}, UnionFind<p, q, k>)
@-}

{-@ find :: forall <p :: UVar -> Bool, q :: IntSet -> Bool, k :: IntMap Entry -> Bool>. uv:UVar<p> -> uf:UnionFind<p, q, k> -> (UVar<p>, {v:UnionFind<p, q, k> | v == uf}) @-}

-- When p holds for a variable, p holds for its representative.
{-@ root :: forall <p :: UVar -> Bool, q :: IntSet -> Bool, k :: IntMap Entry -> Bool>. UVar<p> -> UnionFind<p, q, k> -> UVar<p> @-}
