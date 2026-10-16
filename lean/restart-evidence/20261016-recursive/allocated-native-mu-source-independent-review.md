# Independent review of the checked Mu source adapter

Reviewed: 2026-10-16 04:58 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeMuSource.lean`.
SHA256: `ea90c7ca44ddfbe62fca1c6644726cd9cea84edac0fb56a4cb2506fe4a7bed0b`.
This review made no proof-source changes and ran no build. Root owns the focused build and public probes in this directory.

## Result

No proof defect or old eager-execution substitution was found. The four theorems are conditional source and semantic adapters. They do not assert general checked completion.

## Actual operational prefix

`enter_prefix` (lines 20–33) unfolds the actual checked `NativeDemand.step` on the literal `compileMu` program. The delegated old-native operation is exactly the source `.enter` instruction. This is not an old `Evaluation`, `Produced`, scoped `Step`, or whole-run correspondence premise. Its result retains the literal child `.node` request and `.optionalBinder` continuation. The child domain is the actual result of `Environment.enter` on `before.native.machine.domains`. The checked operations field is unchanged. Actual `advance` retains both native memo tables while updating the domain cache.

This theorem is one enter step after choosing `compileMu`. It does not prove that `compileNode` selects the Mu branch or that the child or binder completes.

## Literal pair, bindings, and bodies

`mu_source_law` (lines 53–114) derives the physical pair equation with `Schedule.pair_encoded` from both Original codecs and both actual identity equations. The same rewritten pair is used for freshness and the actual optional-binder outcome.

The binding list is literally `(Environment.bindings request.left request.right).map Prod.fst`. `bindings` appends the left Mu binding before the right Mu binding. The proof does not replace this list with an arbitrary equivalent domain. `Schedule.entered_key` supplies the exact interned structural key from the explicit valid domain cache.

The child law is indexed by the exact entered domain and `Kernel.body` operands. `body_encoded` uses the fixed source heap's Facts and original operand availability. `original_body` and `unfolded_valid` derive the child Original and model-valid premises. No child input-validity or body-readback oracle is added.

The sound and complete components invoke the child law at that exact request and translate its context with the exact entered-key equation. The complete component retains the same two input derivation ranks and bound. Rank descent and candidate containment remain the independently proved obligations in `MuMeaning`; this adapter does not assume a desired parent-output language law.

## Actual constructor effects

The final step calls `ClosedReceipts.mu_node_law` with the actual `MaybeMu.maybeMu` done equation, initial SemanticHeap, initial GuardedProbeHeap, and available body value. It does not substitute an old eager callback result or assume final semantic readiness. The lower theorem handles the actual optional-binder branch, including the case that returns its body without allocating a binder.

## Remaining caller linkage and completion

The semantic theorem has an explicit generic valid domain `cache` and an explicit optional-binder `before`. It does not equate them to the cache and child-returned heap of one sequential checked run. This does not invalidate the conditional theorem. Integration must instantiate them from the actual enter prefix and returned child state and retain the actual machine, operation-cache, and memo histories.

The caller must also derive the compileNode Mu dispatch premises, freshness, both physical identities, the exact child's contextual NodeLaw from its actual checked trace, and the actual maybeMu completion. The new adapter closes the literal binding-order, pair-encoding, entered-domain, Original-body, and model-body-validity plumbing. It does not close the recursive checked child completion obligation. General checked completion remains open.
