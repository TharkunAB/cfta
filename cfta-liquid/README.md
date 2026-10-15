# cfta-liquid

Refinement generators from Liquid Haskell specifications. The package reads
the specifications that Liquid Haskell verifies, with nothing that is special
to cfta, and gives the generator of `Data.CFTA.Gen.Refinement.Derive` in
cfta-generator. The ordered lists of the Liquid Haskell tutorial:

```haskell
data IncList a = Emp | (:<) { hd :: a, tl :: IncList a }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

{-@ data IncList a = Emp
                   | (:<) { hd :: a, tl :: IncList {v:a | hd <= v} } @-}

{-@ type IncListBounded = IncList {v:Integer | 0 <= v && v <= 1000000} @-}

sortedLists =
    deriveLTAFromLiquid @(IncList Integer) 8 (atom @Integer every) $(liquidSpecifications) "IncListBounded"
```

The generator enumerates a target, here the alias `IncListBounded`: the
datatype at concrete element types, with the refinements of its alias. It is
the generator of `SortedLists.hs` in cfta-generator, with the same ranks.

The translation reads:

- `data` specifications, with the refinements of the fields and abstract
  refinements such as `data RBTree a <l :: a -> a -> Bool, r :: a -> a -> Bool>`.
  The built-in list has the abstract refinement of Liquid Haskell, as in
  `type OList a = [a]<{\fld v -> v >= fld}>`;
- `measure` specifications with their equations. A measure gives an integer,
  a Boolean, or a constructor of a type whose constructors have no fields;
- `type` aliases with type and value parameters, and `predicate` aliases.

A refinement of the elements of a child, such as `tl :: IncList {v:a | hd <= v}`,
holds for each element of the child. The translation derives the least or
the greatest element of the child as a measure. A Boolean measure that the
target requires at the root, such as `isRB` of a red-black tree, and that
holds exactly when a condition holds at each node, becomes a contract of each
node.

The translation is exact or it fails with `Untranslatable` and the position
of the specification. It rejects, for example, a refinement of elements that
is not a conjunction of linear order relations, such as `v /= hd`, a measure
that gives a set, and a measure that Liquid Haskell lifts from a Haskell
function (`measure f` without equations).

A datatype with one measure has it as the measure of `measured`, so its
atomic fields can come from `every`. A datatype with several measures has
named measures, and each one must be one integer for each tuple of children:
its atomic fields come from `elements` or a pool.

The tests derive the examples from specifications of the Liquid Haskell
tutorial and test suite, copied as they are there: the tutorial's `IncList`,
`OList` of `tests/pos/ListSort.hs`, and the red-black trees of
`tests/pos/RBTree_col_height.hs` and `tests/pos/RBTree.hs`.

The package depends on `liquidhaskell-boot`, which pins the version of GHC.
cfta and cfta-generator do not depend on it. Build it with its own project
file:

```sh
cabal build cfta-liquid --project-file=cabal.liquid.project
```
