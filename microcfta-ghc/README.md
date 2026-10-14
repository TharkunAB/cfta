# microcfta-ghc

Component synthesis checked inside GHC's typechecker: Hectare's automaton
(`Data.CFTA.Gen.Synthesis` of [`microcfta-generator`](../microcfta-generator/README.md))
proposes programs over GHC components, and a walk inside GHC's typechecker
checks each program prefix by prefix. The entry point runs inside an
existing `TcM` context, so that a typed-hole plugin can call it.

**Scope: GHC 9.14 only.** The package uses GHC's typechecker API (the `ghc`
library), which changes between major versions; the bound is
`ghc >=9.14 && <9.15`. It is the only package of the repository that
depends on `ghc`.

| Module | Purpose |
| --- | --- |
| `Data.CFTA.GHC.Fits` | The entry point: `streamFits` and `synthesizeFits` for GHC's `TypedHole`, `Candidate`s, and a goal type, and `holeFor` for a driver without a typechecked hole. |
| `Data.CFTA.GHC.HoleFits` | A typed-hole plugin: fits of several components after GHC's own valid hole fits. |
| `Data.CFTA.GHC.Erase` | GHC types as Hectare's first-order types, with the class contexts erased. |
| `Data.CFTA.GHC.Internal.Check` | One step of a program walk in `TcM` on the machinery of GHC's hole fits, and freeze and restore of unification variables; exposed for integration, not covered by the PVP contract. |

## The hole-fit plugin

`Data.CFTA.GHC.HoleFits` is a GHC plugin. For each typed hole, it adds fits
of several components after GHC's own valid hole fits:

```sh
cabal exec -- ghc -fno-code -fplugin=Data.CFTA.GHC.HoleFits test/holes/Holes.hs
```

For this hole of `test/holes/Holes.hs`, GHC alone finds only the definition
itself:

```haskell
countMatches :: (a -> Bool) -> [a] -> Int
countMatches = _
```

With the plugin, GHC 9.14 prints:

```
test/holes/Holes.hs:16:16: error: [GHC-88464]
    • Found hole: _ :: (a -> Bool) -> [a] -> Int
      Where: ‘a’ is a rigid type variable bound by
               the type signature for:
                 countMatches :: forall a. (a -> Bool) -> [a] -> Int
               at test/holes/Holes.hs:15:1-41
    • In an equation for ‘countMatches’: countMatches = _
    • Relevant bindings include
        countMatches :: (a -> Bool) -> [a] -> Int
          (bound at test/holes/Holes.hs:16:1)
      Valid hole fits include
        countMatches :: (a -> Bool) -> [a] -> Int
          (bound at test/holes/Holes.hs:16:1)
        \x1 x2 -> length (map x1 x2)
        \x1 x2 -> length (mapList x1 x2)
        \x1 x2 -> length (dropWhile x1 x2)
        \x1 x2 -> length (filter x1 x2)
        \x1 x2 -> length (takeWhile x1 x2)
   |
16 | countMatches = _
   |                ^
```

The fits come in Hectare's order. `length (map x1 x2)` uses `x1` only
through its type; the parametricity check does not see that.

How the plugin works:

- It takes the candidates that GHC checks for its own fits, and all the
  names in scope (GHC checks only the locals when the hole's type is a type
  variable), as GHC's `tcFilterHoleFits` looks them up.
- A hole of a function type gets its fits as lambdas: each argument of the
  type is a variable that the fit uses once, as in a Hoogle+ query. Other
  holes get fits that use the locals.
- `streamFits` searches in GHC's own `TcM`, on the hole's `TypedHole`: its
  implications give the givens and the level, as for GHC's own checks.
- It drops the fits that GHC finds itself (one identifier applied to the
  arguments in order), and the fits that call the definition that holds the
  hole, because such a fit can loop. Hectare's rule `hectareAvoid` applies:
  a list function is not applied to `[]`.
- A fit that ignores part of itself (`fitIgnoresPart`: it still fits when
  one of its argument subterms has a fresh rigid type) comes after the
  others.
- GHC keeps the first `-fmax-valid-hole-fits` fits (default 6) after the
  plugin. The plugin's driver hook raises that limit by the plugin's number
  of fits, and the plugin puts its fits after as many of GHC's fits as the
  limit was without it. So GHC shows as many of its own fits as before.
- When the search fails, the plugin gives GHC's fits unchanged.

The options apply to each hole:

| Option | Default | Meaning |
| --- | --- | --- |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:size=N` | 4 | The largest fit, in leaves. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:fits=N` | 5 | The number of fits. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:seconds=S` | 1 | The time of the search. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:programs=N` | none | The number of Hectare's programs. |

## How a hole is filled

`streamFits options hole candidates goal accept` runs in `TcM`:

1. Hectare's automaton lists the programs of each size over the candidates'
   erased types (`Data.CFTA.GHC.Erase`), smallest first. A candidate whose
   erased type has a result of any type (`mempty :: a`, `read`,
   `fromIntegral`) is left out of Hectare's library: without its class
   context it would fit every hole. A required candidate (a query argument)
   must occur in every program.
2. Each program is checked in preorder, one leaf at a time, with the parts
   of GHC's `tcCheckHoleFit` (`GHC.Tc.Errors.Hole`). A step is a refinement
   hole fit: the leaf must fit `α1 -> ... -> αk -> goal`, with fresh
   unification variables for its children, by `tcSubTypeSigma` at the level
   of the hole's innermost implication. An obviously insoluble equality
   (`Int ~ Bool`) kills the step without the solver, as GHC's fast path
   does. Otherwise the wanteds of the program so far, cloned, and the hole's
   relevant constraints, cloned, go to `simplifyTopWanteds` under
   `runTcSEarlyAbort`, inside the hole's implications for the givens. The
   solver is skipped while it cannot kill the prefix: when the step brought
   no equality and every wanted still has a unification variable. A prefix
   dies when the solver aborts or leaves a wanted without a unification
   variable; a complete program needs every wanted solved, as in
   `tcCheckHoleFit`. The solver's own unifications and defaulting are
   undone after each call.
3. The walk keeps the checked prefix of the last program. The next program
   restores the unification variables to the longest prefix that the two
   share, and checks only the rest. A failing prefix goes into a trie of
   dead prefixes, and every later program under it is skipped.
4. `accept` gets each fit and returns whether to go on. `synthesizeFits`
   keeps the first `optionFits`.

The hole is GHC's own `TypedHole`: its implications give the skolems, the
givens, and the level of the walk, and its relevant constraints join every
solver call. A hole-fit plugin passes the `TypedHole` that it gets; the
benchmark makes one from a skolemised signature with `holeFor`.

Freeze and restore keep the contents of every unification variable that
the walk reaches, also through filled ones, and write them all back. GHC's
`withoutUnification` only makes the flexible variables flexible again,
which is enough for one check, but not for a prefix kept from one program
to the next: GHC's zonker writes the zonked type back into a filled
variable (Note [Sharing in zonking]), so a filled variable can come to
point past one that the restore makes flexible. The walk also freezes the
unification variables of the goal and the candidates, and leaves every
variable as it found it.

## Running the benchmark and the tests

The test suite `ghc-fits-tests` runs the walk on five Hoogle+ queries with
the Prelude and checks that GHC accepts every fit as a program of the
query's signature. The test suite `hole-fits-golden` compiles
`test/holes/Holes.hs` with the plugin, through the GHC API, and compares
GHC's messages with `test/holes/Holes.golden` (set `GOLDEN_ACCEPT` to write
it again):

```sh
cabal test microcfta-ghc
```

The benchmark runs the 45 Hoogle+ queries of Hectare's evaluation on a
library ladder (the Prelude; then also `Data.List`, `Data.Maybe`,
`Data.Either`, and `Data.Char`; then also `Data.Map`), one child process per
query with a heap limit and a time limit:

```sh
cabal bench microcfta-ghc                            # three queries, 30 s each
cabal run hectare-ghc -- base 120 1400M 8            # rung 2, 8 children at a time
```

The tests and the benchmark need `ghc` on the `PATH` (for `ghc --print-libdir`),
or the variable `GHC_LIBDIR`.

## Limits

- The erased types are first-order: a component with an applied type
  variable other than a `Foldable` or `Traversable` one (`fmap`, `pure`,
  `(>>=)`, `traverse`) has no erased type, so Hectare never proposes it.
- A unification variable of the goal becomes a rigid constant in the erased
  goal, so Hectare proposes only programs that keep it abstract.
- There is no defaulting: a program that needs `Num` defaulting is rejected.
- Many valid programs of the real Prelude are degenerate. `fitIgnoresPart`
  finds those that ignore a subterm by parametricity (`const xs n`), but not
  those that ignore it through its type (`length (map f xs)`) or that are
  bottom (`foldl1 asTypeOf []`). Hectare's order decides which come first.
- The plugin relies on its driver hook to raise `-fmax-valid-hole-fits`. A
  GHC API client that adds the plugin as a static plugin must call
  `initializeSessionPlugins` before GHC reads the modules, as the `ghc`
  program does.
