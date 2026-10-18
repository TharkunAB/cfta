# Common reader support for one actual node-Mu unfolding

Frozen on 2026-10-18. Source: `SourceCurrentCommonReaderBinderSupport.lean`, SHA256 `1f1b667d94cb71da9b95ec1a001ba35d88abb1018c7c82c565d9443536b7f2ea`.

## Proven result

The public `node` theorem starts from initial `Ready`, an available stored Mu with a literal ordinary-node body, and existing `WarmSupport`. It constructs the actual unfolding with `StoredReconstruction.execute`. It derives the returned heap, `Keeps`, output availability, and the exact warm replay at that heap. The result is ordinary. Existing support, the Mu, and its result form `WarmSupport` at this returned reader.

The child hypothesis concerns only actual warm executions of strict original stored children under the exact sparse self substitution. It permits an output in existing support or the same recursive Mu. It does not assume that the whole parent is settled, that its successors are supported, or that two parent outputs are related. Arbitrary nested Mu children are allowed when this strict hypothesis is available.

`StoredNodeExpansion.node_warm` supplies actual ordered row calls and surviving row origins. `StoredCallsReplay.replay` supplies the exact child calls at the final heap. The proof selects their original child occurrences and derives the strict size bound. `WarmSupport.grows` transports existing support through actual `Keeps`. The exact warm Mu unfolding supplies its single epsilon successor. The returned ordinary value has no epsilon successor and has a reflexive unfolding.

## Constructed use

`CommonReaderKernels.open_used` builds the open source `binder true (node [mk 0 false [var 0, var 1]])` with external reference `uninterned 9`, from the empty heap. The source Mu has a free marker, positive stored binder depth, and a used recursive local. Its body has a self child and the marker child. Primitive marker support is derived directly. The strict child hypothesis follows from the two literal reference execution equations. The theorem then invokes the public producer.

The constructed conclusion retains actual cold and warm unfolding equations, initial `Ready` and availability, exact final `Keeps` and output availability, and final support. It also proves `before.nodes.next < after.nodes.next`. This is a real allocation. The fixture does not supply future support or a future unfolding equation. A private checked witness and a public theorem have identical statements. The full public proof prints this exact alias.

## Remaining boundary

This is one source-derived support extension for an ordinary node body. It does not prepare all available open Mu values. In particular, the closed lower-depth preparation argument cannot be applied to arbitrary open captured Mu values. A captured open Mu can be re-encoded during reconstruction. `InternedStoredRawIdentityBoundary.observed` shows that physical identity reconstruction need not hold for an open raw unused Mu. This is not an observation or Haskell failure.

General changing-capture congruence still needs a source-derived strict child support and relation argument for arbitrary active nested binders. Available values and `Ready` alone have not been proved to supply that argument. This component makes no general termination or reader equality claim. No executable defect or Haskell repair was found.

## Evidence

Selected source check: `common-reader-direct-2`, exit 0 and literal zero-byte log. Selected canonical check: `common-reader-canonical-1`, exit 0, 577 jobs, no warnings. Selected public group: `common-reader-public-1`, one complete declaration, proof, and axiom report.

Selected fixture check: `common-reader-kernels-2`, exit 0 and literal zero-byte log. Selected constructed group: `common-reader-kernels-public-1`, one complete declaration, proof, and axiom report. Both groups use all eight print options. Their only reported axioms are members of `propext`, `Classical.choice`, and `Quot.sound`. Effective limits are memory.max = memory.high = 4294967296, memory.swap.max = 0, with a 5-minute cap and Lean 4.34.1.

Failed direct attempt 1 and failed fixture attempt 1 remain immutable. Their errors concern elaboration only. No strict or public failure is selected. This component counts one new public theorem and one constructed theorem. It adds no auxiliary pair. The separate independent review and all shared root files are excluded from this manifest.
