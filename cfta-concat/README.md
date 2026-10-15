# cfta-concat

Refinements, contracts, and measures for the refinement generators of
[`cfta-generator`](../cfta-generator/README.md), written as monomorphic
Haskell functions. The concat plugin
([Compiling to categories](http://conal.net/papers/compiling-to-categories/),
Elliott, ICFP 2017) compiles each function to the `Formula` or `Expr` of the
refinement logic of [`cfta`](../cfta/README.md).

**Scope: GHC 9.14 only.** `concat-plugin` depends on the `ghc` library, so
this package is not in `cabal.project`, and no other package of the
repository depends on it. Build it with `cabal.project.concat`.

## A predicate as Haskell

The sorted lists of `cfta-generator/examples/SortedLists.hs`, with the
contract, the measure, and the conditions as plain Haskell:

```haskell
-- This module compiles with -O -fplugin=ConCat.Plugin.
import ConCat.Rebox ()
import Data.CFTA.Concat (symbolic)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen

inRange :: Integer -> Bool
inRange v = 0 <= v && v <= 1000000
{-# INLINE inRange #-}

ordered :: Integer -> Integer -> Bool
ordered element restHead = element <= restHead
{-# INLINE ordered #-}

listHead :: Integer -> Integer -> Integer
listHead element _ = element
{-# INLINE listHead #-}

nilHead :: Integer -> Bool
nilHead v = v == 1000001
{-# INLINE nilHead #-}

sortedLists :: LTAGen.LTAGen [Integer]
sortedLists = LTAGen.recurUpTo 8 $ \rest -> LTAGen.oneof [nil, cons rest]
  where
    nil = LTAGen.leaf [] "nil" (symbolic nilHead)
    cons rest =
        LTAGen.measured "cons" (symbolic ordered) (symbolic listHead) $ LTAGen.do
            x <- LTAGen.every `LTAGen.satisfying` symbolic inRange
            xs <- rest
            LTAGen.pure (x : xs)
```

`symbolic ordered` has the type `Expr -> Expr -> Formula` of a contract,
`symbolic listHead` has the type `Expr -> Expr -> Expr` of a measure, and
`symbolic inRange` is a `Refinement`. The formulas are equal to the formulas
of the expression language in the example, so the generator has the same
cardinality and the same ranks. The same functions check the generated values.

A free variable becomes a constant, so a refinement can take bounds at run
time: `symbolic (\v -> low <= v && v < high)`.

## The rules for a compiled function

- It is monomorphic, over `Integer`, `Int`, `Bool`, `()`, pairs, and
  functions of these. A list is an opaque value that only measures read.
- It has no recursion. A recursive measure is written for each constructor,
  as the measures of the refinement generators are.
- Its definition is visible to the plugin, for example with an INLINE pragma.
- The module that calls `symbolic` compiles with `-O -fplugin=ConCat.Plugin`,
  and its component depends on `concat-classes`, `concat-plugin`, and
  `ghc-prim`, because the plugin loads modules of these packages.

When the plugin cannot compile a call, the call stays in the program and
stops it when it runs. Two guards find such calls:

- `-fplugin-opt=ConCat.Plugin:showResiduals` lists them when the module
  compiles, and `-fplugin-opt=ConCat.Plugin:failResiduals` stops the build
  with an error (Tritlo/concat 58eabf45 or later). The test suites of this
  package use both options.
- A test that forces each compiled formula fails. The test suites of this
  package force each formula.

## Measures

`Data.CFTA.Concat.Measure` has the length of a list as a primitive: `len xs`
is `length xs` on values and `uninterpreted "len" [xs]` of the logic on
formulas, as the measure `len` of `Data.CFTA.Gen.Synthesis.Liquid`. The
precondition of `head`, `\xs -> len xs >= 1`, compiles to `len xs >= 1`.

The module has the orphan instance `OkType [a]` of the plugin's class
`ConCat.OkType.OkType`. The plugin composes morphisms only on the types of
that class. Without the instance, it unfolds `len` to `length`, and it cannot
compile the recursion.

## Building and testing

`cabal.project.concat` takes the concat packages from Tritlo/concat, branch
`ghc-9.14`, at commit 58eabf45: the port to GHC 9.14.1, with the plugin
option `failResiduals`.

Build and test:

```sh
cabal build --project-file=cabal.project.concat cfta-concat --enable-tests
cabal test --project-file=cabal.project.concat cfta-concat
```

The `acceptance` suite needs Z3 on the `PATH`, as the generator examples do.

| Test suite | What it checks |
| --- | --- |
| `acceptance` | SortedLists, SafeDivision, LiquidPairs, and RedBlackTrees of `cfta-generator/examples` with compiled predicates and measures: equal formulas and shown text, equal cardinality, equal values at every rank or at 205 ranks, and the predicates hold on those values. |
| `measure` | The precondition of `head` with `len`: the formula `len xs >= 1`, and the predicate on values. |

## Limits

- No recursion, and no match on the constructors of a recursive type: one
  function for each constructor.
- Compile time only: the functions are monomorphic, with INLINE pragmas.
- GHC 9.14.1 only, the version that the concat fork supports.
- The result of the plugin depends on GHC's simplifier. The test suites cover
  the predicates of the four examples, not every Haskell function.
