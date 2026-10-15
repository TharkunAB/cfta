# Changelog

## 0.1.0.0 - Unreleased

Before release, the package was called `microcfta-ghc`.

Initial version, for GHC 9.14 only (`ghc >=9.14 && <9.15`).

- `Data.CFTA.GHC.Fits`: `streamFits` and `synthesizeFits` fill a GHC
  `TypedHole` in `TcM`. Hectare's automaton proposes programs over the
  `Candidate`s, size by size, and a walk inside GHC's typechecker checks each
  one prefix by prefix with the parts of GHC's `tcCheckHoleFit`, with a trie
  of dead prefixes. The walk is the one of `Data.CFTA.Gen.Synthesis.Walk`
  (in `cfta-generator`), with GHC's frames and the table of verdicts as
  its checker. `holeFor` makes a hole from skolems and givens.
  `Options` bound the size, the fits, the programs, and the seconds, carry
  Hectare's pruning rules, and take a report after each size and a trace of
  each program. `Statistics` give the time of Hectare's construction,
  reduction, and listing, and of the checks, and the typed terms that
  Hectare listed (`statisticsRuns`). With `optionCurried`, Hectare's types
  are curried, and every bound type variable of kind `* -> *` ranges over
  the type heads in scope at which each of its classes can have an
  instance (`mayHold` of `Data.CFTA.GHC.Internal.Check`, the test of the
  fast path), so `length (lookup k xs)` is proposed; no candidate is
  specialized then. With `optionOnlyDefaulted` too, such a variable that a
  program does not determine takes only its default, the list type, as
  under `ExtendedDefaultRules`, and the check of a complete program has
  those rules, so `length (pure x)` fits.
- `Data.CFTA.GHC.Session`: a GHC session for a program, with the imports in
  scope as in GHCi. `withSession` and `withSessionOptions` start it, with
  more packages by name or identifier, more package databases, more flags,
  and, with `sessionCompile`, the interpreter backend and linking in memory.
  `typeOfExpression`, `declare`, `compileExpression`, `candidatesOf`, and
  `inSession` use it; `fitsForSignature` and `inSignatureHole` run a search
  on the hole of a signature. `ghc-fits`, the tests, and the benchmark use
  it.
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
  every hole once erased. An applied rigid type variable (`f a`) erases to
  a type constructor. `higherKinded` and `typeHeads` give the variables and
  the heads for the specializations of `streamFits`: a component with a
  higher-kinded type variable is proposed at each type head of the query
  whose class constraints GHC solves under the hole's givens.
  `eraseCurried`, `eraseHead`, and `curriedClasses` give the curried types.
- `Data.CFTA.GHC.Internal.Check`: one step of a program walk as a refinement
  hole fit (`tcSubTypeSigma`, GHC's fast path for insoluble equalities, and
  `simplifyTopWanteds` under `runTcSEarlyAbort` inside the hole's
  implications, with GHC's pure unifier for equalities that are surely
  apart and the instance environment for class constraints that no
  instance can match; neither runs under a given equality, only nominal
  equalities can be apart, a quantified given provides the class of its
  head, and the classes that GHC solves without instances go to the
  solver), freeze and restore of unification variables, and
  `StateKey`, the state of a walker up to the names of its unification
  variables. The walk keeps the verdict of each step by state and leaf, and
  skips the steps and the solver calls whose verdict it knows.
- The `ghc-fits` executable: the programs of a type signature over the
  exports of some modules, checked in GHC's typechecker.
- The `hole-fits-golden` test: GHC's messages for a module with holes,
  compiled with the plugin.
- The `hectare-ghc` benchmark: the 45 Hoogle+ queries on a library ladder
  read from GHC's exports, one child process per query. The queries come
  from the sublibrary `cfta-generator:hoogleplus`.
