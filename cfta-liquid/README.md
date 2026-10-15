# cfta-liquid

Refinement generators from Liquid Haskell specifications. The package reads the
`data` specification, the measure, and the refinement aliases of a datatype,
and gives the generator of `Data.CFTA.Gen.Refinement.Derive` in
cfta-generator:

```haskell
{-@ measure hd :: IncList -> Integer
        hd Emp = 1000001
        hd (Cons x xs) = x
  @-}

{-@ data IncList = Emp
                 | Cons { x :: {v:Integer | 0 <= v && v <= 1000000}, xs :: {v:IncList | x <= hd v} }
  @-}

data IncList = Emp | Cons Integer IncList
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

sortedLists = deriveLTAFromLiquid @IncList 8 (atom @Integer every) $(liquidSpecifications)
```

The generator is the generator of `SortedLists.hs` in cfta-generator, with the
same ranks. The translation is exact or it fails with `Untranslatable`: a
node of a liquid tree automaton has one integer, so the translation takes one
measure of the datatype, and it takes linear formulas over the fields and the
measure.

The package depends on `liquidhaskell-boot`, which pins the version of GHC.
cfta and cfta-generator do not depend on it. Build it with its own project
file:

```sh
cabal build cfta-liquid --project-file=cabal.liquid.project
```
