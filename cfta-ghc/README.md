# cfta-ghc

Component synthesis checked inside GHC's typechecker: Hectare's automaton
(`Data.CFTA.Gen.Synthesis` of [`cfta-generator`](../cfta-generator/README.md))
proposes programs over GHC components, and a walk inside GHC's typechecker
checks each program prefix by prefix. The entry point runs inside an
existing `TcM` context, so that a typed-hole plugin can call it.

**Scope: GHC 9.14 only.** The package uses GHC's typechecker API (the `ghc`
library), which changes between major versions; the bound is
`ghc >=9.14 && <9.15`.

| Module | Purpose |
| --- | --- |
| `Data.CFTA.GHC.Fits` | The entry point: `streamFits` and `synthesizeFits` for GHC's `TypedHole`, `Candidate`s, and a goal type, and `holeFor` for a driver without a typechecked hole. |
| `Data.CFTA.GHC.Preference` | Learn corrections to corpus scores from preferred programs and fixed pools of GHC-checked alternatives. See [Train preferences between valid hole fits](docs/hole-fit-preferences.md). |
| `Data.CFTA.GHC.HoleFits` | A typed-hole plugin: fits of several components after GHC's own valid hole fits. |
| `Data.CFTA.GHC.Erase` | GHC types as Hectare's types, curried or first-order, with the class contexts erased. |
| `Data.CFTA.GHC.Internal.Check` | One step of a program walk in `TcM` on the machinery of GHC's hole fits, and freeze and restore of unification variables; exposed for integration, not covered by the PVP contract. |

## The synthesizer

`ghc-fits` lists the programs of a type signature over the exports of some
modules, each checked in GHC's typechecker, best first:

```sh
$ cabal run ghc-fits -- -m Prelude -m Data.Maybe '[Maybe a] -> a -> a'
\x1 x2 -> foldl fromMaybe x2 x1
\x1 x2 -> foldl' fromMaybe x2 x1
\x1 x2 -> foldl const x2 x1
\x1 x2 -> foldl' const x2 x1
\x1 x2 -> foldr seq x2 x1
```

The signature can have a class context (`Eq a => a -> [(a, b)] -> Maybe b`),
which gives the givens of the search. Each argument of the signature is a
variable that a program uses once. `-m MODULE=Q` imports a module qualified,
and `-p PACKAGE` exposes a package. `--size`, `--fits`, and `--seconds`
bound the search (by default five leaves, ten fits, ten seconds).
`--first-order`, `--only-defaulted`, and `--no-type-domains` are the plugin's
options `first-order`, `only-defaulted`, and `no-type-domains` below, and
`--rank`, `--rank-pool N`, `--rank-seconds S`, and `--model NAME` its ranking (see "Ranking
the fits with a decision model"). The figures of the search go to the
standard error. The Hoogle+ ladder of
`hectare-ghc` is its benchmark.

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

The fits come in Hectare's order, which depends only on the hole: the
holes before it in the module do not change it. `length (map x1 x2)` uses
`x1` only through its type; the parametricity check does not see that.

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
- A fit with the normal form of an earlier fit is skipped: the bodies of
  the components unfold from GHC's unfoldings (`Data.CFTA.GHC.NormalForm`),
  so `flip map x2 x1` is `map x1 x2`, and `fst ((,) x y)` is `x`.
- A fit that ignores part of itself (`fitIgnoresPart`: it still fits when
  one of its argument subterms has a fresh rigid type), or whose normal form
  drops an argument (`fitDropsArgument`: `const xs n` is `xs`), comes after
  the others.
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
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:model=FILE` | none | Score fits with a corpus or trained preference file. See [the preference guide](docs/hole-fit-preferences.md). |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:model-search=best-first` | rerank a pool | Search in score order with mode (b). |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:first-order` | off | Hectare's first-order types (see Limits), in place of its curried types. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:only-defaulted` | off | A variable of kind `* -> *` that a fit does not determine takes only its default, the list, and the check has `ExtendedDefaultRules`. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:no-type-domains` | off | A variable of kind `Type` with classes takes any type. By default it takes only the types in scope at which the instances of those classes can hold, following the instance contexts, so `maximum` does not have a goal `a` or `(a, Int)` without `Ord a`. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:normal-forms=off` | on | Keep the fits with the normal form of an earlier fit. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:rank` | off | Order the fits with a decision model (below). |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:rank-pool=N` | 50 | The number of fits that the model orders. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:rank-seconds=S` | 60 | The time limit of a question to the model. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:rank-model=NAME` | `nimble-v3:9b-q4_K_M` | The model on the server. |
| `-fplugin-opt=Data.CFTA.GHC.HoleFits:rank-keep-alive=D` | `0` | How long the server keeps the model loaded after a request. |

### Ranking the fits with a decision model

With `rank`, a decision model orders the plugin's fits
(`Data.CFTA.GHC.Rank`, through the package `decision-model`). It needs a
running [Ollama](https://ollama.com) on `http://localhost:11434` with a
model that has the capability "decision": by default Nimble v3
(`nimble-v3:9b-q4_K_M`), an external model under its own license, or
another with `rank-model`. The plugin searches for `rank-pool` fits that use
every part, asks the model one question about them (which fit a programmer
most likely intends, with the definition, the hole's type, and the local
variables), and shows the best `fits` in the model's order; the other fits
come after them, in the plugin's order. The other `rank-` options need
`rank`. When the model does not answer, or does not answer in
`rank-seconds`, the fits keep the plugin's order.

The scores of a model that stays loaded depend on the requests before
them. So by default the server loads the model for each ranked hole
(`rank-keep-alive=0`): a hole gets the same order on each compile, and a
ranked hole takes about 5 s (the first one also loads the model from the
disk). With `rank-keep-alive=5m` the model stays loaded, and a question
takes 0.3 to 0.7 s, but the order of a hole can then depend on the holes
before it; the plugin unloads the model at the end of the module.

On the 23 Hoogle+ queries of rung 1 that the search solves, with Nimble v3
and the defaults, the expected fit is first for 16 queries (9 in the
plugin's order) and in the first five for 21 (12).

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
   The walk also keeps the verdict of each step by the walker's state and
   the leaf (`StateKey`: the goals, the wanteds, the relevant constraints,
   and the unification variables of the context, zonked, with the
   unification variables numbered in order). A step that failed before
   from an equal state is skipped without a check; a step that passed
   before does not call the solver. Two subprograms of the same type lead
   to equal states, so the steps after them repeat.
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

## A session from a program

`Data.CFTA.GHC.Session` gives a program a GHC session with imports in scope,
as GHCi has them. It gives the type of an expression, takes declarations,
compiles an expression to a value, and searches the fits of a signature, as
`ghc-fits` does:

```haskell
import Control.Monad.IO.Class (liftIO)
import Data.CFTA.GHC.Fits (defaultOptions, fitProgram)
import Data.CFTA.GHC.Session

main :: IO ()
main = withSession ["import Prelude"] $ \session -> do
    candidates <- candidatesOf session [Import "Prelude" Nothing]
    Just typ <- typeOfExpression session "undefined :: (a -> b) -> [a] -> [b]"
    _ <- fitsForSignature session defaultOptions candidates typ ["f", "xs"] $ \fit ->
        False <$ liftIO (print (fitProgram fit))
    pure ()
```

`withSessionOptions` takes more packages (by name or by unit identifier),
more package databases, and more flags. With `sessionCompile`, the session
uses GHC's interpreter and links in memory, so that `compileExpression`
gives values; a program that shares values with the session exposes its own
units, as its QuickCheck, with `sessionPackageIds`.

## Running the benchmark and the tests

The test suite `ghc-fits-tests` runs the walk on five Hoogle+ queries with
the Prelude and checks that GHC accepts every fit as a program of the
query's signature. The test suite `hole-fits-golden` compiles
`test/holes/Holes.hs` with the plugin, through the GHC API, and compares
GHC's messages with `test/holes/Holes.golden` (set `GOLDEN_ACCEPT` to write
it again):

```sh
cabal test cfta-ghc
```

The benchmark runs the 45 Hoogle+ queries of Hectare's evaluation on a
library ladder (the Prelude; then also `Data.List`, `Data.Maybe`,
`Data.Either`, and `Data.Char`; then also `Data.Map`), one child process per
query with a heap limit and a time limit:

```sh
cabal bench cfta-ghc                            # three queries, 30 s each
cabal run hectare-ghc -- base 120 1400M 8            # rung 2, 8 children at a time
cabal run hectare-ghc -- base 120 1400M 8 stackoverflow   # the 19 Stack Overflow queries
```

With the normal forms, a fit with the normal form of the expected solution
counts as the solution. `HECTARE_GHC_NORMAL_FORMS=off` turns them off.

The ranking has two steps, so that the model gets one request at a time.
With `HECTARE_GHC_POOL=P`, each query goes on past its expected fit to `P`
fits that use every part, and prints them in a `pool,` line. Then
`hectare-ghc --rank FILE SIZES... [--model NAME] [--keep-alive D]` asks the
model about each pool, for each number of options and with the options in
one order and in both orders, and prints the rank of the expected fit in
the plugin's order, in the order of size, and in the model's order:

```sh
HECTARE_GHC_POOL=255 cabal run hectare-ghc -- prelude 120 1400M 6 > pools.csv
cabal run hectare-ghc -- --rank pools.csv 20 50 255 --keep-alive 0
```

Keep the pools and the rows out of the repository: they are outputs of a
model under its own license.

The tests and the benchmark need `ghc` on the `PATH` (for `ghc --print-libdir`),
or the variable `GHC_LIBDIR`.

## Limits

- The erased types are curried. A type variable of kind `* -> *` (`fmap`,
  `pure`, `(>>=)`, `length`, both variables of `traverse`) ranges over the
  type heads of kind `* -> *` in the candidates' types and the query at
  which an instance of each of its classes can hold, the list among them.
  So `length (lookup k xs)` is proposed, and the space is larger than the
  first-order one: more programs to check, and more fits before the
  expected one. A type head that no candidate and no query has is not
  tried.
- With `first-order`, the erased types are first-order. A component with a
  higher-kinded type variable gets an erased type only at the type heads of
  the query (`Maybe` in `Maybe a`, or `m` in `Monad m => m (m a) -> m a`)
  whose class constraints GHC's solver discharges under the hole's givens;
  not at the list head, which the list functions cover. A `Foldable` or
  `Traversable` variable becomes a list.
- A unification variable of the goal becomes a rigid constant in the erased
  goal, so Hectare proposes only programs that keep it abstract.
- There is no defaulting: a program that needs `Num` defaulting is rejected.
  With `only-defaulted`, the check of a complete program has GHC's
  `ExtendedDefaultRules`, so `length (pure x)` fits.
- Many valid programs of the real Prelude are degenerate. `fitIgnoresPart`
  finds those that ignore a subterm by parametricity (`const xs n`), and
  `fitDropsArgument` those whose normal form drops an argument, but not
  those that ignore it through its type (`length (map f xs)`) or that are
  bottom (`foldl1 asTypeOf []`). Hectare's order decides which come first.
- The normal forms know each component whose interface has an unfolding
  without recursion or a class dictionary. These depend on how the library
  was compiled (none at `-O0`), and they can change with a GHC release. Two
  programs that are equal through a recursive component
  (`reverse (reverse xs)` and `xs`) keep their own normal forms.
- The plugin relies on its driver hook to raise `-fmax-valid-hole-fits`. A
  GHC API client that adds the plugin as a static plugin must call
  `initializeSessionPlugins` before GHC reads the modules, as the `ghc`
  program does.
