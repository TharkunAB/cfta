# Normalized source constraints and complete native Sized queries

Updated: 2026-10-14 22:22 CEST.
Proof: `064cd013`, after `634a3c40` and `0215ed02`.
Source base: `7bfb69d1` (PR #129). All work remains local.

## Constraint preservation

`InternedFreshOrdinaryConstraintHeap.Heap` states that every stored edge key
satisfies a constraint predicate. `SyntaxValid` checks each original input
annotation. The actual edge request installs its checked annotation. Node and
union normalization, body filtering, and Mu reservation retain the edge cache.
`build_heap`, `buildMany_heap`, and `buildEdges_heap` follow the actual repaired
source schedule. They cover complete and pending outcomes, every probe call,
cache hits, and actual reserved bodies. They do not assume cache validity,
successful construction, or a semantic language equation.

`InternedFreshOrdinaryStoredConstraintHeap.encode_valid` proves the invariant
for the actual encoded substitution plan. Resident ordinary edges supply the
exact original constraints. Ordered child encodings and open nested Mu bodies
retain the invariant. `execute_heap` and `unfold_heap` then prove preservation
through actual repaired stored substitution and unfolding.

`MergedFreshOrdinaryConstraintHeap` follows actual bounded cold-reader control.
It retains the edge-cache invariant through direct ordinary paths, ordered
union closure, and every recursive unfolding cache. An exhausted bound also
retains the invariant. No successful read is assumed.

`SourceFreshOrdinaryColdSharedRows.Trace.constraint_heap` carries this fact
through actual finite shared traversal. `table_constraints` uses resident
canonical edge records to establish the predicate at every exact raw row.
The finite map lookup preserves original row order and constraint payloads.

## Complete normalized source entry

`SourceFreshOrdinaryNormalizedNativeSized.complete` starts from actual closed
source construction and checked original annotations. The annotation predicate
is `ActiveOption constraint.equalities`. It derives initial cache normalization,
Ready, root availability, and closedness. It derives normalized final rows
through the actual cold trace. No final rowwise normalization certificate,
raw child-key closure, final-cache metadata, scan equality, product-language
equation, or native completion is supplied.

The result has finite stable actual cold traversal and finite actual native
compilation, subject to reached-query word checks. It retains the compiler's
literal reference result and actual returned cache. Every accepted output has
finite exact distinct classes at every node-count size, exact counts and
decoder order, literal optimized/reference class equality, finite reference
classes, distinct size-major prefixes, exact physical-root support, rank
coverage, and both global distinct-term rank/unrank inverse laws.
`SourceFreshOrdinaryNativeCompiler.query_inverses` also retains bounded
selection/ranking and position/replay inverses for the same actual execution.

## Complete query record and finite preparation

`SourceFreshOrdinaryNativeCompiler.api_record` derives literal equality of
the complete optimized and reference `SourceSizedDispatcher.Api` records.
It covers terms, counts, unranking, and ranking. Signed size and rank inputs
retain their existing behavior. The proof derives plainness and distinctness
from the actual native compiler result. It does not assume a passing abstract
graph gate or another scan equality.

`finite_prepass` derives one finite source minimum-size prepass, its stable
fixed point, and finite count/decoder evaluation at every node-count size.
The same prepared table supports all sizes. These are source-model execution
certificates. They do not count primitive Haskell or machine instructions.

## Input and resource boundaries

`SourceCompactGuards.normalize_active` establishes the annotation invariant
for actual array normalization. `combine_active` establishes it for actual
equality combination. Empty stored equality classes also satisfy it. Semantic
guards need no positivity premise at input; the compiler's actual precheck
rejects constrained rows before ordinary native overlap checks.

The public `EqConstraints` pattern in
`cfta/src/Data/CFTA/Equality/Constraint.hs` does not normalize its input.
Its comment states that `mkEqConstraints` sorts classes and the pattern does
not. The public `PathEClass` pattern also accepts a raw path set. Therefore
arbitrary raw pattern-built equality values do not establish `ActiveOption`.
The new source entry explicitly checks original annotations. It does not
claim that every public raw constructor produces a normalized value. This is
an input boundary, not an observed runtime defect or a new source repair.

Reached-query native `Ranges` remains explicit. It checks current requests
and only suffixes reached after continuing actual calls. The next target is
to derive these word checks from actual source cache/key bounds where possible.
Read `SourceRecursiveIntersectionNativeWordRanges`, `SourceRecursiveIntersectionMemo.KeySafe`,
`SourceRecursiveIntersectionEdgeMemo.KeySafe`, and `IntersectionFlatMemoKey.Safe`.
Keep a finite-capacity premise when required. Arbitrary natural-number caches
cannot fit a fixed native word width. Do not replace actual-prefix checks
with completion assumptions or bounds on arbitrary future heaps.

Concrete container extraction, lazy runtime scheduling, and external solver
correctness retain their stated boundaries. The model retains guard payloads
after the check; checked structural equality justifies Haskell's erasure to
unit. This is semantic correspondence, not verified Haskell record extraction.
Older constructor and equality targets remain secondary. Preserve all earlier
proofs, counterexamples, repairs, fixtures, and marked drafts.

## Validation

The pinned Lean 4.34.1 aggregate build passes 1,532 jobs and checks dependencies
of 44,248 theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Log: `/tmp/mcfta-normalized-native-sized-20261014-audit.log`.
Focused build logs use these names under `/tmp/`:

- `mcfta-constraint-heap-20261014-build.log`
- `mcfta-stored-constraint-heap-20261014-build.log`
- `mcfta-cold-reader-constraint-heap-20261014-build.log`
- `mcfta-cold-table-constraint-heap-20261014-build.log`
- `mcfta-normalized-native-sized-20261014-build.log`
- `mcfta-native-compiler-api-20261014-build.log`

No new warning was introduced. The older unused `inputs` warning remains.
No production Haskell code changed. The same source base already passed 645
source examples, five updated probes, and formatter checks. These checks were
not repeated for the Lean-only changes.
