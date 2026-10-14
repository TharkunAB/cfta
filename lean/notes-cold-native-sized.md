# Actual cold native compilation and exact Sized queries

The later [normalized source proof](notes-normalized-native-sized.md) derives
row normalization from checked original annotations through actual construction
and cold traversal. It also proves complete query-record equality and one
finite minimum prepass for every size. It supersedes the normalization target
below. Raw pattern-built equality values retain an explicit input boundary.

Updated: 2026-10-14 22:09 CEST.
Proofs: `634a3c40` and `0215ed02`.
Source base: `7bfb69d1` (PR #129). All changes remain local.

## Compiler input and complete execution

`SourceFreshOrdinaryColdCyclic.input` constructs the cyclic compiler input
from the actual finite cold table. It derives root membership from completed
row support. It copies every symbol, ordered child, and complete constraint.
`original_eq` proves literal equality with the guarded finite-key automaton.
`checked_structural` uses the actual constraint precheck to derive literal
equality with structural rows. `checked_ambiguity` then derives the exact
reference ambiguity Boolean. `root_language` derives the independent guarded
language of the identical original physical root.

`SourceFreshOrdinaryNativeCompiler.Execution` models empty, open,
constrained, ambiguous, and accepted branches in source order. Only the last
two branches run the actual ordered native ambiguity scan. They retain its
exact final cache. The accepted branch uses finite canonical refinement and
the source transition order. `complete` derives finite execution and literal
reference compiler-result equality, including errors. `execution_correct`
covers every actual completed execution. No whole scan equality, product
equation, exact product-row adapter, or native completion is supplied.

`class_correct` derives finite optimized class evaluation, exact distinct
accepted terms at each node-count size, counts, decoder order, and literal
reference-class equality. `query_inverses` derives position/replay and bounded
term-rank inverses, selection totality, and exact rejection. `reference_laws`
derives finite reference classes, distinct bounded prefixes, nondecreasing
node-count order, rank coverage, and both global distinct-term inverses.

## Derived source metadata

`MergedFreshOrdinaryExposureLive` proves empty-child exclusion for actual
ordinary, union, and Mu exposure. Its fuel induction follows actual closure
control and unfolding caches. The semantic heap retains the stored ordinary
live-edge invariant. It does not assume a completed reader or a row shape.

`SourceFreshOrdinaryColdClosed.table_closed` combines this exposure result
with actual row replay, closed child payloads, and completed child declarations.
It derives raw finite child-key closure. `NoEmptyBelow` and a supplied raw
closure proof are no longer required at the composed cold entry.

`SourceFreshOrdinaryColdNativeTable.constructed` derives the initial ready
native state, root availability, and closedness from actual closed source
construction. `collect` derives finite stable cold traversal, the exact map
domain, resident and replayed rows, declared children, raw child-key closure,
and the ready native state for the first overlap query. Advancing the machine
retains both native memo tables. No caller supplies these final invariants.

`SourceFreshOrdinaryColdNativeSized.complete` composes that actual traversal
with finite native compilation. Every successful result has finite exact
classes, counts, decoder order, literal reference/optimized class equality,
distinct size-major prefixes, exact physical-root support, rank coverage,
and both distinct-term inverse laws. All final-cache and table premises are
derived inside this theorem. Root free variables are empty by its closed-root
premise. The finite table is an auxiliary readback certificate for empty roots.
It does not assert that the Haskell compiler traverses an empty root.

## Remaining source boundary

Normalized equality classes remain explicit at actual input rows through
`SourceCompactGuards.ActiveOption`. Arbitrary raw `Constraint` values in the
model do not establish this invariant. Prove it from the public source
constraint constructors and their preservation through actual cold exposure.
`normalize_active` and `combine_active` already establish the local array
normalization and combination facts. Do not assume all raw class lists are
normalized or change the public constraint precheck to make the proof easier.

`Ranges` requires checked native words only at reached queries and continuing
actual suffixes. It is not a supplied completion certificate. Derive this
contract from source cache/key bounds where possible. Do not replace it with
a bound on arbitrary future heaps. That contract can be stronger than the
actual finite scan.

The model retains interpreted guard payloads after the precheck. Haskell
erases those payloads to unit. The checked structural equality justifies this
semantic correspondence; it is not a verified extraction of Haskell records.
Concrete containers, lazy runtime scheduling, and verified Haskell extraction
remain outside the current theorem. Older constructor and equality work stays
secondary. Preserve all counterexamples and marked drafts.

## Validation

The pinned Lean 4.34.1 build passes 1,526 jobs and checks dependencies of
44,192 theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Log: `/tmp/mcfta-cold-native-sized-20261014-audit.log`.
Focused logs use `/tmp/mcfta-cold-native-sized-20261014-build.log`,
`/tmp/mcfta-cold-native-table-20261014-build.log`,
`/tmp/mcfta-cold-closed-20261014-build.log`, and
`/tmp/mcfta-exposure-live-20261014-build.log`.
The old unused `inputs` warning remains. These modules introduce no warning.
No production Haskell code changed. The existing 645 source examples, five
updated probes, and formatter checks passed on this same source base. They
were not repeated for these Lean-only additions.
