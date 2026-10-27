# Actual native arity primitives

The immutable source is `drafts/v1/SourcePruningEnumerationNativeArityPrimitives.lean`, 139 lines, SHA256 `616d843851e076a2b4900b73572e48142d3d0803ad526dabd37aae6e0af1df31`. Root's first strict check passes with exit 0 and an empty raw log. The installed source has the same bytes. Root owns compilation, installation, and the pending serial installed build. This reviewer ran no compiler, build, tests, Git command, network call, or repository edit. No previous frozen bundle was changed.

The module has one definition and nine public theorems. It imports the current ArityOrigins, actual MaybeMu, and actual NativeDemand sources. The review pins seven whole source inputs and ten focused literal cuts, 336 cut lines. Whole copies preserve provenance. Only the listed cuts define the source-review scope.

The definition `WorkFits job state` follows the constructor requests that actually execute. Its edge case checks `Fits key.constraint key.children.length`, then checks the continuation at the exact `edgeStep` return value and cache. Its node case follows the exact `nodeStep` return. It has no universal premise over other possible constructor values or native continuations. `edgeStep_heap` uses the existing first-writer `record_cases` rule. `work_heap job state heap checked` then preserves Heap through this actual finite work.

The convenience theorems are `makeEdge_fits symbol constraint children state checked`, `makeNode_fits edges state`, `makeUnion_fits values state`, and `filter_fits name value state`. The raw edge condition is the supplied guard at the actual child count. Node, union, and bare-self filtering emit no edge-key request. These conditions describe only the current constructor work. They do not certify a later native action.

`optionalBinder_heap key body state facts heap available` proves Heap at the exact `maybeMu` outcome state. It uses the actual `maybeMu_eq` reconstruction equation and ArityOrigins `encode_checked` and `build_heap`. Those existing producers already retain arity through edge, node, union, and self-filter operations. The result covers both done and pending outcomes. It does not require completion, a future callback law, Room, or a final Heap premise. Facts, Heap, and Available refer to the actual current input heap and body.

`step_work_heap job next state heap checked` and `step_optionalBinder_heap key body next state facts heap available` expose the result at the actual `SourceEqualityNativeDemand.step` heap. They retain the runtime's exact state projection through native advance and Demand lift. The optional-binder wrapper covers both the yielded done branch and the blocked pending branch. The `next` continuation is arbitrary because the one step only returns it. No theorem says that continuation preserves Heap when later executed.

The invariant remains a property of stored canonical keys. Generic work can use an arbitrary identify callback. This module does not infer payload coherence, Ready, Safe, capacity, semantic acceptance, Caller invariants, or memo validity from Heap. Existing native input receipts must supply those separate facts where needed.

The module does not invert a rich native trace or an accepted child walk. It does not prove arity for a complete native query or recursive history. Actual generated query code, its accepted edge creation, raw child-list lengths, request-frame effects, and the full trace composition remain separate producer obligations. The primitives add no universal continuation or output-satisfaction admission to those producers.

This bundle remains open until Root supplies the installed-build receipt. No further source edits are planned.
