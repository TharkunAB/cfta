# Main refresh: named measures and generic decoding

Source main: `1eb4ab05`, merged without rewriting at `271284df`.
Backup: `backup/formalize-before-main-1eb4ab05-20261015-1237`.
The starting snapshot is `/tmp/mcfta-result-memo-start-20261015-1236/`.
The HTTPS fast-forward pull discovered the new source before proof edits.

## Source changes and correspondence

The merge adds named measures to constructor refinement generation and a
red-black tree example. `measuredBy` validates arity, reads named integer
conjuncts from children, resolves named child measures and arithmetic, and
requires a point-valued result. `uninterpreted` builds the existing App term.
The new measure-building surface has no full source correspondence proof.
The lower full formula and constraint semantics remain available.

Generic constructor decoding now checks type and constructor name. It leaves
child arity to the field decoder. It no longer compares stored constructor
field metadata. The integer and Int decoders now use decimal parsing; Int
conversion uses fromInteger and can wrap outside its range. Canonical encoded
values retain their intended decoding. Arbitrary parser behavior and malformed
constructor metadata need a fresh implementation bridge. The existing abstract
codec laws are retained, and do not prove these new parser branches.

The Liquid Fixpoint adapter now infers integer function sorts for undeclared
applied names. The query antecedent, consequent, and ambient assumptions supply
applications in that order. Application heads precede their argument applications.
The last occurrence supplies an arity. The implementation does not reject
conflicting arities at this step. Explicit and generated declarations retain
precedence. Unapplied undeclared names retain Int.

`SourceAppliedDeclarations` models the complete collection order, last-winner
lookup, inferred sorts, declaration exclusions, and injective name encoding.
`SourceSolverAppliedPreparation` supplies the current raw and encoded preflight.
It proves full preparation transport, unchanged rejection cases, and complete
application-free compatibility. Embedded arithmetic-core inputs are included.
`SourceSizedLiquidAppliedAmbient` proves the actual full declared domain and
encoded unsatisfiability equivalence with independent ambient query meaning.
It retains applications, casts, quantifiers, assumptions, and mixed sorts.
`SourceSolverAppliedPublic` connects the current per-call result and finite
work relation to public exact classes, canonical sequence, distinct size order,
and both signed inverse laws. Correct external replies and finite attempts
remain separate contracts. Historical preparation/public modules remain intact.
They target their historical source unless application-free compatibility applies.

`SourceSizedFiniteKeysAppliedLiquid` runs the current encoded callback on the
actual original-state raw trim and state folds. `encoded_correct` and
`encoded_finite` retain their separate contracts. `encoded_exact` and
`encoded_complete_exact` connect successful outcomes to the common full API laws.
The older `SourceSizedFiniteKeysPublic` and `SourceSizedFiniteKeysNativeLiquid`
encoded endpoints remain historical. The current endpoint does not retarget
`SourceColdSharedRows.Trace.liquid_correct`,
`SourceFreshOrdinaryColdSharedRows.Trace.liquid_language` or `.liquid_exact`, or
`SourceFreshOrdinaryLiquidEntry.Execution` or `.open_result`. Those wrappers
still use historical preparation and meaning. Their current-source composition
remains open beyond the proved application-free compatibility.

The optimized interned core, equality operations, Sized definitions, and older
constructor/equality proofs are preserved. The merge changes no Lean proof.
The new source-comparison modules are additive.

## Validation

The strict Nix build includes all libraries, executables, test suites, and
benchmarks. All six test suites pass: 687 examples and the golden suite.
Fourmolu checks the changed Haskell files. Cabal-gild and cabal check pass for
all four packages. The new red-black named-measure example agrees on counts
through size 10 and values at 205 ranks. SameRanks is its helper module.
An initial command guessed an incorrect executable name; the corrected
`cfta-red-black-measures` invocation passes. No Haskell source was changed
locally after the merge. Existing linker warnings remain build observations.

Logs:

- `/tmp/mcfta-main-1eb4ab05-build-20261015.log`
- `/tmp/mcfta-main-1eb4ab05-tests-20261015.log`
- `/tmp/mcfta-main-1eb4ab05-format-metadata-20261015.log`
- `/tmp/mcfta-main-1eb4ab05-examples-20261015-corrected.log`

These checks are component evidence. They do not prove whole-library source
correspondence. Decision-model and GHC scheduling remain outside full coverage.
Read [the recursive result-memo note](notes-result-memo-worker.md) for the
current next proof target.
