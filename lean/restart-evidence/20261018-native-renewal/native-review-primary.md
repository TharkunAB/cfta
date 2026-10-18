# Independent selected primary origin review

Reviewed at 2026-10-19 00:04 CEST. I read the complete final
SourceCurrentSelectedPrimaryOrigins module, SHA256
8852c579427f1398fce9076ae99754857eb3f62dba87a32da2644caaf5bddd25.
I also read the literal record and path Scan workers, the false-primary
replay interfaces, and UnionNormalScan with its projection and gate cases.
I found no material issue. This review starts no Lean process. It reuses
three public declarations and adds no constructed declaration.

selected_class consumes a literal successful record Scan equation. It
requires initial NativeOperationHeap.Good and availability of the same
input forest. In the false-primary branch, the singleton Scan equation
returns exactly that literal record and the actual first gate's returned
state. ParentOperationInvariants.scan supplies its physical Effect.
Class replay then puts the false certificate at the completed suffix heap.
The inductive suffix uses the actual intermediate Good and the original
forest's availability retained by Keeps. No future callback, Ranges, Reads
or outer return is an input.

Both true-primary cases drop the current record. A true secondary gate
continues with the suffix. A false secondary gate runs the actual seeded
query and conjunction decision. A true decision stops with no kept record;
a false decision continues. The proof reconstructs the exact singleton
prefix for the physical Effect in each case. It does not classify a
secondary refusal as a false-primary certificate. Repeated records or
equal path lists require no uniqueness assumption.

The forest values remain the original Scan inputs through all these
branches. Query and gate calls can change the heap, but the proof does not
substitute a projected result or a rewritten forest for those inputs.
selected_path applies false_class_paths to this exact forest and a path in
the retained record. Both certificate endpoints are the actual final Scan
heap. The explicit DecidableEq conversion uses instance uniqueness. It
does not change the trace, forest, path or heaps.

selected_source additionally requires initial UnionNormal. It applies
UnionNormalScan.records to the literal Scan and obtains normality at its
exact successful endpoint. The path certificate and the historical
normality fact therefore have the same final anchor. This discharges the
normality mismatch identified during the earlier draft review. The proof
does not infer UnionNormal from Good or SemanticReady. The initial
normality premise remains explicit.

UnionNormalScan follows each bounded gate, query and decision in worker
order. Its bind laws retain the reached stopping state on failure and
enter only an actual successful next stage. Record mapPaths changes only
the record representation of the result. It does not assert that Scan
leaves the initial heap unchanged. The selected-origin endpoints use this
all-outcomes invariant only at their supplied successful Scan endpoint.

The new producer makes the false primary receipt and historical normality
available for subsequent projection routing from the same original
forest. It does not itself run that projection, establish initial outer
source ancestry for generated values, compose native Mu origins, bound
renewal, exclude active owners, or prove general completion. It gives no
Haskell refinement or defect claim.

Selected final receipts are selected-primary-direct-8,
selected-primary-canonical-1 and selected-primary-public-1. The direct log
has zero bytes and its immutable source exactly matches production.
Canonical one completed all 1801 jobs with only the existing
InternedFreshOrdinaryClosedCompletion unused-input warning. Public one
passes the hardened check for all three complete signature/proof/axiom
pairs, all eight printer settings, no omissions and only standard axioms.
All three receipts record the 4 GiB maximum and high limits, zero swap,
pinned Lean 4.34.1 and the five-minute capped command.

This report and its separate pins do not change the frozen 62-pin native
component. Mutable fixtures, peaks, shared selections, authority documents
and unselected root attempts are excluded from these review pins.
