# Changelog

## 0.1.0.0 - Unreleased

Initial version, for GHC 9.14 only (`ghc >=9.14 && <9.15`).

- `Data.CFTA.GHC.Fits`: `streamFits` and `synthesizeFits` fill a GHC
  `TypedHole` in `TcM`. Hectare's automaton proposes programs over the
  `Candidate`s, size by size, and a walk inside GHC's typechecker checks each
  one prefix by prefix with the parts of GHC's `tcCheckHoleFit`, with a trie
  of dead prefixes. `holeFor` makes a hole from skolems and givens.
  `Options` bound the size, the fits, the programs, and the seconds, carry
  Hectare's pruning rules, and take a report after each size and a trace of
  each program. `Statistics` give the time of Hectare's construction,
  reduction, and listing, and of the checks.
- `Fit` tells whether a fit ignores part of itself (`fitIgnoresPart`): it
  still fits when one of its argument subterms has a fresh rigid type, so by
  parametricity it cannot use that subterm. `synthesizeFits` puts such fits
  last. `hectareAvoid` is Hectare's rule that a list function is not applied
  to `[]`.
- `Data.CFTA.GHC.HoleFits`: a typed-hole plugin
  (`-fplugin=Data.CFTA.GHC.HoleFits`). After GHC's own valid hole fits, it
  gives fits of several components, which `streamFits` finds in GHC's `TcM`
  on the hole's `TypedHole`. Options: `size`, `fits`, `seconds`, and
  `programs`.
- `Data.CFTA.GHC.Erase`: GHC types as Hectare's first-order types, with the
  class contexts erased, and `anyResult` for the components that would fit
  every hole once erased.
- `Data.CFTA.GHC.Internal.Check`: one step of a program walk as a refinement
  hole fit (`tcSubTypeSigma`, GHC's fast path for insoluble equalities, and
  `simplifyTopWanteds` under `runTcSEarlyAbort` inside the hole's
  implications), freeze and restore of unification variables, and
  `StateKey`, the state of a walker up to the names of its unification
  variables. The walk keeps the verdict of each step by state and leaf, and
  skips the steps and the solver calls whose verdict it knows.
- The `ghc-fits` executable: the programs of a type signature over the
  exports of some modules, checked in GHC's typechecker.
- The `hole-fits-golden` test: GHC's messages for a module with holes,
  compiled with the plugin.
- The `hectare-ghc` benchmark: the 45 Hoogle+ queries on a library ladder
  read from GHC's exports, one child process per query.
