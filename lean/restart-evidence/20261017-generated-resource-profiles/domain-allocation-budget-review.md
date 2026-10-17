# Initial syntax allocation budget

The production module proves node and edge counter bounds for every actual `InternedFreshOrdinaryConstruction.build`, `buildMany`, and `buildEdges` outcome. The initial finite syntax supplies the complete budget. The theorems need only the edge-key equality instance. They require no valid heap, available environment, successful return, future callback result, or output profile.

## Budget and actual schedule

The six budget functions recurse on the original syntax. Empty and variable syntax have zero budget. A node adds one possible node allocation to the sum for its original rows. A union adds one possible node allocation to its original member sum. Every raw row adds one edge allocation after its children. A binder has node budget `3 * nodeBudget body + 4` and edge budget `3 * edgeBudget body`.

The binder budget pays for three complete executions of its original body: Depth, the repaired ordinary probe, and the fresh interned body. Each execution also pays for `withoutSelfReference`, which can emit at most one node request and no edge request. The fourth node credit pays for the Mu reservation. The repaired ordinary level can depend on the actual Depth value. This does not affect the original body's uniform allocation bound.

The proof follows the exact stopping state. A pending child stops its suffix. A hit on a complete Mu returns without a new reservation. A hit on a reserved incomplete Mu returns pending without running the fresh body. A miss pays for one actual `Cache.intern` reservation and its actual fresh callback. Candidate installation and first-writer readback change only record maps. Smart cleanup changes only the returned value. All these cases remain inside the same static bound, including a pending fresh-body result.

The shallow constructor bounds reuse existing actual request accounting. `makeNode` and `makeUnion` allocate at most one node each. `makeEdge` allocates at most one edge. The bounds count real possible allocations; they do not use the difference of final counters as a purported initial estimate. They remain valid with arbitrary captured values and warm records.

## Validation

The final production source is SHA-256 `1df14599b09a4c93dfacb0ea2a0172aa16353b091213f825f245de6ec0c9e224`. Strict pinned Lean 4.34.1 attempt 5 has exit code 0 and an empty log. Root canonical build `canonical-fresh-allocation-budget-1.log` completes 116 jobs with no diagnostics. All six budget functions and three bound theorems have imported full explicit signature and axiom probes. The final public log has nine pairs and no diagnostics.

Three imported integration pairs pass in `domain-allocation-budget-kernels-4.log` without errors, warnings, or `sorryAx`. Kernel reduction uses `decide +kernel`, not native evaluation, for its concrete proof claims. The axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

`nested_callbacks` constructs an actual raw outer binder. Its node contains its own reference and a nested raw binder. The nested binder contains a union, its own reference, and a node that captures the outer reference. The literal execution finishes from empty caches with 19 node identities and six edge identities. The initial syntax budgets are 37 nodes and 12 edges. This exercises nested reconstruction and both probes. It does not use a supplied completed execution.

`reserved_pending` constructs the actual reserved Mu key in an otherwise empty cache. The binder executes its two probes and returns the exact pending key with the whole reserved heap unchanged. The all-outcome theorem bounds that stopping state. No completed record or future body is assumed.

`repeated_nested` derives the first actual nested return from the literal execution, applies existing exact constructor replay, and constructs the actual two-element `buildMany` result in that returned heap. The second execution retains the complete state and both counters. The same serial execution satisfies the original summed list budget.

All failed source attempts and raw logs remain preserved. Production attempts 1–4 contain elaboration or syntax failures. Kernel attempts 1–2 contain failed elaborations. Kernel attempt 3 passes but reports one unused simp argument; attempt 4 removes that argument and is the final clean probe. The separate evaluation attempt 1 used a reserved Lean identifier; attempt 2 records the concrete returned counts. That evaluation is supplementary evidence; the three integration theorems prove the claimed facts in the kernel.

## Scope

This module closes initial syntax bounds for constructor identity counters, including arbitrary nested binders, union normalization, warm hits, and pending outcomes. `InternedFreshMuUnfoldBudget` instead proves unfinished-record progress and does not supply these initial counter bounds. This component does not bound total evaluation time, list processing, heap payload size, or arbitrary interleaved host schedules. It does not yet derive a uniform budget for every generated query or complete the full constrained reduction. A caller that encodes a generated value must still bound that actual encoded syntax or apply this exact syntax budget at its own initial body.
