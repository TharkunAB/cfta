# Main refresh: derived refinement generators

Source main: `6fe34ab815d41bd282e46903afc693e9671bd2d3`.
Preserving merge: `9f8d3afc`.
Backup: `backup/formalize-before-main-6fe34ab8-20261015-1559`.
The pre-merge proof checkpoint is `7c5f4367`. Its 2,624-file snapshot is
`/tmp/mcfta-native-validity-checkpoint-20261015-1555/`.

The opening branch pull fetched this main update while formalize remained
current with its own tracking branch. The closing ancestry check detected
the pending main update. The merge retained both entries in the one
changelog conflict. No proof history was rewritten.

## Source changes and coverage

The six upstream commits add two public modules, new tests and examples,
and package registration. Generic now exports Description constructors.
Its codec and discovery bodies do not change. The optimized interned core,
equality operations, Sized, existing refinement combinators, Expression,
and LiquidFixpoint implementations are unchanged by the upstream delta.
The local equality traversal repair and its changelog entry remain. These
are the only package differences from the new main tree.

`Data.CFTA.Refinement.Symbolic` gives Bool/Formula and Integer/Expr
interpretations of comparisons and Boolean operations. `Measures` reads
named child measures as uninterpreted terms or concrete NodeIntegers.
Concrete reads fail when the requested component is absent. Value/formula
agreement, named-measure environments, user totality, and partial lookup
behavior need source correspondence proofs. Existing symbolic counting
modules do not prove this new interface.

`Data.CFTA.Gen.Refinement.Derive` derives recipes from HasFTA metadata and
HasLTA invariants. Its source contracts include rightmost atomic overrides,
annotation order/arity/errors, constructor-name lookup, bounded metadata
discovery, strongly connected type groups and recursion depth, constructor
recipe selection, movement of atomic contract conjuncts, actual codecs,
and exact member ranks. It also evaluates invariant functions on generic
constructor placeholders and on concrete encoded values. These new source
bridges are uncovered. Existing Generic, core formula, and generator
combinator proofs retain their earlier scope.

Read the source audits at
`/tmp/mcfta-main-6fe34ab8-source-audit-20261015.md` and
`/tmp/mcfta-main-6fe34ab8-derived-audit-20261015.md`.

## Verified source counterexamples

The standalone [counterexample](repro/DerivedAnnotationBoundaries.hs) uses
only public APIs. It is not part of a package test suite.

`annotationFormulas` omits named measures. Two annotations that set m to
zero and one have equal projections. After the same m = 0 root predicate,
their finite generators have cardinalities two and one. A second unchanged
constructor keeps both generators nonempty. This refutes the documented
claim that equal projected formulas and terms imply the same generator.

For `data Strict = Strict !Integer`, a HasLTA invariant that discriminates
with the documented `Strict{}` pattern throws the placeholder-field error.
The invariant reads its field integer from the supplied integer list.
Constructing the generic strict-field placeholder forces the error before
that pattern can distinguish the constructor. The existing tests use lazy
fields and do not cover this case. The source behavior remains unchanged.

Run the retained file against the exact local library units:

```sh
nix-shell --run 'env PATH=/usr/bin:$PATH cabal exec -- runghc --ghc-arg=-package-id --ghc-arg=cfta-generator-0.1.0.0-inplace --ghc-arg=-package-id --ghc-arg=cfta-0.1.0.0-inplace lean/repro/DerivedAnnotationBoundaries.hs'
```

Log: `/tmp/mcfta-derived-boundaries-final-20261015.log`.
The earlier package-name invocation selected a hidden package incorrectly.
Its failure is tooling evidence. The exact-unit invocation verifies both
source counterexamples.

## Validation and remaining work

The strict Nix build covers all libraries, executables, test suites, and
benchmarks. All six existing suites pass: 696 examples and the golden
suite. Fourmolu checks the five changed upstream Haskell files and formats
the standalone counterexample. Cabal-gild and cabal check pass for all four
packages. The cabal-gild command reports a deprecated --input option; the
package checks report no package warnings. Existing linker warnings remain.

The Lean audit passes 1,975 jobs and 50,686 dependency checks with only
propext, Classical.choice, and Quot.sound. All pre-merge proof definitions
retain their hashes. Logs:

- `/tmp/mcfta-main-6fe34ab8-build-20261015.log`
- `/tmp/mcfta-main-6fe34ab8-tests-20261015.log`
- `/tmp/mcfta-main-6fe34ab8-format-metadata-20261015.log`
- `/tmp/mcfta-main-6fe34ab8-lean-audit-20261015.log`

The next checked-native target remains derivation of native InputsThrough,
semantic finish receipts, internal word ranges, sidecar field allocation
coverage, and a candidate-parametric Mu language invariant. Read
[the running and field note](notes-native-field-running-invariants.md).
Both new frontend APIs add full-scope obligations. Whole-library
correspondence remains incomplete. Exact Sized classes, finite execution,
sequence, distinct size order, and both signed inverse laws remain separate.
