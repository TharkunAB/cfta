# Proposed native positive-support rebase

Prepared at 2026-10-21 03:41 CEST. Frozen after the final public API cue at 03:46 CEST. This is a source-only plan. It has no new Lean job or theorem claim.

The smallest additive theorem rebases the existing public `SourceCurrentNativeRequestPositivePositions.Support`. It keeps the native state and every full captured request unchanged. It changes only the source heap used by its conditional input premises.

Proposed concrete signature, with the same native Symbol and Guard aliases as the position module:

```lean
rebase (source later : Heap) (state : Native width Symbol Guard)
  (sourceFacts : Facts source) (laterFacts : Facts later)
  (growth : Grows source later)
  (issued : Extends source.nodes.issued later.nodes.issued)
  (origins : SourceCurrentConstrainedCapCheckedJointOrigins.Stored source state)
  (supported : SourceCurrentNativeRequestPositivePositions.Support source state) :
  SourceCurrentNativeRequestPositivePositions.Support later state
```

This is approximately 50–80 source lines including the imports and native aliases. It needs no new public predicate, execution induction, sourceWeight law, or result-availability premise. The proposed theorem has not been checked.

For each node family `Valid`, retain its `bounded` and `linked` fields. Rebuild only `checked`, using the same actual handle/cell lookup to obtain `origins.nodes handle cell found`. Suspended and evaluating cells have a trivial `CellSpec`. For a returned cell, introduce the later conditional depth, bindings, input and cap premises. Apply `CheckedJointOrigins.bindings_back Plain source later growth issued laterFacts` to the same origin's `scope.bindings`. Apply that same `NodeOrigin.inputs_back` to recover the earlier input premise. The old returned positive-position law then proves the required conclusion unchanged. `PositiveAt`, both complete operands, and the requested path do not depend on the source heap.

The edge family is the same construction. Its `EdgeOrigin.inputs_back sourceFacts` uses the actual old resident rows to recover availability for each original ordered child. The root guard disjunction, full returned row, exact child index and residual positive path remain unchanged. Source facts are needed here. The existing weight rebase is not required because `EdgePos` contains no sourceWeight conclusion.

Do not use `FlatMemoThunk.Valid.map` directly unless its callback can retain the actual lookup. Its current callback is `forall cell, first cell -> second cell`, whereas the origin is indexed by an actual handle/cell lookup. Reconstructing the three `Valid` fields is the short route and preserves the same state.

# Pairing with the existing call entry

At a real later query entry `before`, set `later := before.native.machine.heap`. The following existing facts serve distinct purposes:

- `CheckedJointRebase.rebase Plain source before.native sourceFacts growth issued good.native origins oldJoint` yields the old joint store and all captured origins at that exact later heap.
- The proposed theorem yields positive `Support` at the same heap for the same native tables.
- `Context Plain later before.native.machine` is rebuilt from actual current physical facts, semantic heap, and guard heap, with reflexive source growth and issued extension.
- `AllocatedRecursivePrefixState.initial later (SourceInventory.domains later) before good semantic rfl` provides the `Current` used by the new public positional `call`. It uses the actual current domain cache as its initial cache. It does not claim that the cache is empty.
- The current causal `NativeMuPublication.History empty later` remains a separate actual receipt. Neither `Grows` nor this rebase constructs it.

The next query still needs its actual checked Trace, closed current resident operands, and finite `Cap Plain depth` input premises. The proposed rebase does not construct query completion or caps for arbitrary generated operands.

# Actual producers of the required captured origins

The capture premise is actual provenance, not a desired warm result law:

1. `CheckedJointOrigins.initial_stored` derives it for empty native memo tables.
2. `CheckedJointOriginTrace.Trace.origins` transports it along the SAME admitted physical Trace. It takes initial Good/SemanticReady, source growth and issued extension, actual control field facts, a source admission certificate, and the original finite-input interpretation. It returns final origins for all memo phases and the final admission certificate. The Trace can be unfinished; it needs no future root return.
3. `CheckedJointInventoryCold.cold_complete` returns an `InventoryQuery.Receipt` whose `origins` field is derived from the receipt's SAME actual query trace. `InventoryQuery.of_receipt` is the concrete extraction point. `InventoryQuery.generated_complete` rebases the old joint and origin facts before deriving the next receipt.
4. `ConstrainedCapCurrentNative.step` derives origins from the SAME supplied actual Target query step and retains them in `At Plain after`. `GeneratedQueryFrameResources.complete` also returns a `Frame` whose `origins` field is derived from its SAME query receipt. The Frame is defined in `ConstrainedCapGeneratedQueryResources`.
5. `OuterInitialPrefix.reached` returns a SAME reached-state Frame under its actual initial Context/Frame/Fits/Carrier/Inputs/Room premises. `OuterInitialActual.node_call` and `ActualClassSemanticReads.class_reads`/`fold_reads` also return actual Frames. These are useful outer sources of captured origins. They do not establish this premise from an arbitrary Good state or from bare Reached alone.

The current positional `call` returns Support, its actual joint Return, result support and causal history. It does not return captured origins. A sequential consumer must keep an existing correlated Frame/Receipt, or apply `Trace.origins` to that SAME actual trace with its actual admission certificate. It must not infer origins of newly captured requests from returned Support or bare heap growth.

# Sharp boundary

This theorem reinterprets proved laws of actual old returned cells. Original here is the physical fixed-source `Original` shape and captured read scope. It is not a lexical original-program binder occurrence or source Path. The theorem does not relate observations through opaque Mu, change forest values, prove a later query will return, or prove outer completion. The source heap can contain genuinely generated closed operands, but their current availability and finite caps must still come from actual independent execution facts.

The retained final position source is `e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727`. The owner confirmed that Support/call/request and the source bytes were final. This plan does not claim a new checked proof or a new printer/axiom pair.
