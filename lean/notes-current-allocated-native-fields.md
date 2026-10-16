# Loaded equality fields through checked native execution

Source main is 894a74af. No Haskell source changes in this increment.
The optimized interned core and earlier constructor and equality proofs stay.
This note advances the field-cache target in notes-current-conjunction-worklist.md.

## The representation gap

Cached raw equalities do not imply a successful read-only load. In an empty
operation cache, the normalized Top field has load = ok none. A kernel
example proves that it does not satisfy FieldAvailable. Actual sentinel
allocation then supplies the canonical empty field and its successful load.
No finite cache is assumed to contain every possible future conjunction.

## Actual allocation and continuations

SourceCurrentConjunctionFieldAllocation derives FieldAvailable from actual
same-cache constructor receipts. Its completed construction, conjunction,
ready intersection, and sentinel endpoints derive valid growing operations
and the exact returned raw field. Read-only lookup adds no allocation.

SourceCurrentAllocatedNativeCodeFields indexes each emitted annotation by
the current equality-operation cache. Actual growth retains each existing
load. Sequencing, source node compilation, raw constructors, and optional
binding preserve these receipts. New accepted child code uses the actual
combined field receipt. Sentinel code uses the actual empty-field receipt.

SourceCurrentAllocatedNativeFieldClosure follows the actual checked body.
body_complete derives both successful original loads from resident initial
Fields and constructs the next body continuation. The ready branch uses
the actual conjunction allocation. Rejected and mismatch branches allocate
the sentinel field. Existing continuation facts grow to the returned cache.
Every actual step retains the physical heap's loads at that returned cache.

The guard equality instance is the literal source structural comparison.
It matches the checked Demand and Control definitions. An arbitrary inferred
equality instance does not identify their operational run expressions.

SourceCurrentAllocatedNativeFieldExecution derives all reached normalized
checks from the stronger initial loaded-field invariant. Its finite execution
endpoint retains actual validity, physical extension, original records,
equality-operation growth, loaded fields, and the actual yielded continuation.
Errors and blocked outcomes retain their real returned states. OutcomeFields
certifies a continuation only for a yielded outcome. It does not certify the
stored continuation of a blocked outcome.

## Gates and projection

SourceCurrentAllocatedGateFields preserves the same loaded-field invariant
through actual primary and secondary gates, nodeEdges, heads, and supported
projections. Its equality-operation state stays literally unchanged.
An actual false class trace derives finite projection for a selected proper
path at its exact anchor. Unrelated original siblings can remain open.
These endpoints derive their effects. They supply no future Fields premise.

## Remaining query and caller work

The checked execution plan still includes current work operands, reached
word checks, and actual NodeProduced or EdgeProduced receipts at finish
controls. The new proof does not derive general checked native completion.
Initial Fields remains an initial representation invariant. Per-field actual
construction now derives it locally. Original whole-heap allocation histories
still need composition with the native entry.

The older scoped Fold and Seeded use a different native step without the
operation cache. Checked rejection can skip child work that the older
compiler performs. Do not infer equal returned heaps or erase that difference.
Define the reached allocation-aware native query with both returned states.
Derive its completion, checked input receipts, independent language result,
SemanticReady, and CostHeap. Then use the same final heap and operation cache
to enter the new conjunction memo and a new current Scan. The historical
intersection-based Scan is not current execution evidence.

General constrained outer completion, whole enumeration and import, broader
APIs, lazy demand and publication, concrete containers, machine capacity,
runtime identity, concurrency, and every separate Sized contract remain in
scope. The typed-rule validation, codec, callback, and helper-order boundaries
remain open. This component does not finish the full-library goal.

## Validation

The pinned full audit passes 2,247 jobs and 55,211 theorem dependency checks.
Thirty-nine public axiom probes, twenty-one endpoint signatures, and thirty-one
kernel examples pass. Only standard foundations and the old unused-input
warning occur. Independent review found no cache-indexing or circularity defect.

Five new modules and two additive Audit imports preserve every older non-Audit
Lean file. Haskell checks are reused from the preceding typing checkpoint:
the strict Nix build, six suites with 763 examples plus golden, the post-repair
224 generator examples, Fourmolu, and Cabal-gild. Source files are unchanged.
No new test suite is added. Evidence uses /tmp/mcfta-allocated-* and
/tmp/mcfta-current-allocated-*. The prior sixteen marked external drafts stay.
