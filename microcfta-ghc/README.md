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
| `Data.CFTA.GHC.Erase` | GHC types as Hectare's first-order types, with the class contexts erased. |
| `Data.CFTA.GHC.Internal.Check` | One step of a program walk in `TcM` on the machinery of GHC's hole fits, and freeze and restore of unification variables; exposed for integration, not covered by the PVP contract. |

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

The test suite runs the walk on five Hoogle+ queries with the Prelude and
checks that GHC accepts every fit as a program of the query's signature:

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
- Many valid programs of the real Prelude are degenerate, such as
  `const xs n` and `head []`; Hectare's order decides which come first.
