# Native renewal handoff after child retention

Reviewed 2026-10-19 13:12 CEST. This is a read-only source audit. It adds no Lean runs, public pairs, constructed pairs, or proved theorem. The separate edge component remains frozen.

## Completed ordinary handoff

`SourceCurrentRecursiveEventPathOrigins.fold` produces `PathOrigin observation.readAfter (residual.map Int.ofNat ++ observation.path) event row`. It retains the actual event execution and the remaining observation. It does not assert a projection of the whole event.

For a nonempty path, `PathOrigin.child` gives an epsilon-origin parent row, its exact natural child index, and the remaining path of that child. `SourceCurrentNativeOriginViewBranches.returned` normalizes the captured native cell at checked reader `q`. The physical origin view stays separate from `q.heap`.

`SourceCurrentNativeReaderChildRetention.ordinary` now derives the actual paired child request, `Retained childAfter.native q.native`, its returned cell and its SAME historical node writer at `q`. It also derives both strict operand-child mass bounds. The edge receipt comes from `SourceCurrentNativeEdgeWriterRetention.edge_writers`; its retention field is inside the same body/finish existential. Thus the earlier warm edge writer is covered. No child-entry History is needed. `NativeReferenceOrigins.forwarded` uses History at `q`.

This closes the missing ordinary child provenance. It does not decrease the mass of the generated output, and a nonplain final row does not imply that an earlier path row is nonplain.

## Exact Mu producer/consumer mismatch

There are two different executions.

1. `NativeOriginExposure.Unfold view entry storedBody depth ordinary row` executes the SELECTED stored body at the physical observation view, with the selected Mu as its local replacement. The returned state can grow. Its origin tail remains at the ORIGINAL view.
2. `NativeMuBodyOrigins.Body q ...` retains the SAME captured compiler writer and its entered-domain request on `body request.left` and `body request.right`. That call returns `bodyValue`, followed by the literal `maybeMu pair bodyValue` call.

Neither receipt identifies the selected stored body with `bodyValue`, or transfers an observed row of the stored unfolding to an observed row of that body-query return. A cache hit can select an earlier publication with different source syntax and captures.

`NativeMuSourceHandoff.returned` does not bridge this gap. Its premise is an indexed PHYSICAL `nodeEdges result` row. Its conclusion gives `RowAt bodyValue original`, then either a literal origin or the first opaque Mu publication on a union path. It cannot consume an arbitrary full epsilon origin of a retained Mu. `RowAt` beneath a Mu is a syntactic occurrence, not an observational origin. `NativeRequestProbes.request_probes` gives equality of the complete selected depth/ordinary probes, not equality of the selected body and the current callback.

The next semantic producer must therefore retain the selected older writer, the current optional-binder callback schedule, and the actual observed stored-body execution together. It must derive guarded row/ordered-child provenance between those executions. It must not assume that provenance, whole-result `Same`, or a supplied parent rank.

## Missing causal heap history at the event interface

`ClassEventExecutions.Source` retains native memo `NativeEdgeWriterGrowth.History` before and after the query. It does NOT retain `NativeMuPublication.History empty eventHeap`, or an issued-name `NativeMuIssuedHistory.Path empty eventHeap`.

This distinction is material. Native memo `History.initial` accepts any physical machine with empty native memo tables. Its `advance` constructor receives only physical `Grows`. Hence this memo History cannot establish an actual earlier Mu publication or issued-name extension. `Source.later` composes heap Keeps only. It does not add such history.

`NativePublicationTrace.from_history` can extend an already supplied publication history through the actual query trace. It cannot construct that initial history from memo History. Actual publication history must be threaded from the source-built initial heap through the actual Required/Head/class/fold effects. Issued history is additionally needed for the existing `CausalStoredMuGenerators.selected/complete` interfaces. Their same-reader endpoint requires warm actual reconstructions; `complete` instead produces a later reader. Neither result supplies guarded row clauses at an arbitrary old observation view. Their generated membership and root-profile/Empty agreement are weaker than the missing guarded provenance.

## Concrete next proof target, unchecked

First derive a causal event-history producer from INITIAL physical publication provenance and the literal observed worker receipts. It should return the publication history at the captured query return and an actual forward history to the observation view. Derive issued extension from the actual effects if an issued Path consumer is used. Do not infer either history backwards from the view or from four-table Grows. This is a prerequisite, not the semantic Mu bridge itself.

Then prove a selected-winner guarded readback clause. Given that causal history, the actual current `maybeMu` schedule, and the actual finite observation of the selected stored Mu, derive a source-row/ordered-child continuation through the CURRENT ordinary callback and body-query receipt, or an explicitly identified lexical replacement backedge. Keep the original observation view and every actual execution interval. A callback row may require child substitution; literal equality of complete rows is not an adequate universal target. The all-guard row fields and ordered child provenance are the substantive conclusion. If reconstruction needs a later heap, retain that actual interval and prove the needed supported observation transport; do not silently rebase `Origin`.

A proof should use actual publication chronology for older payloads and strict ORIGINAL syntax for callback cases. The returned raw value's stored depth is not a valid publication induction index. The actual finite epsilon witness can control exposure steps. Arbitrary transitive closure of source generators is unsound; `LiteralNormalizationSimulation.Relation` permits only one source step with genuine Below normalization before and after it. These are proof obligations and a proposed architecture, not a checked progress theorem.

## Reference ancestry and global limit

`NativeOriginViewBranches.reference` retains an exact bound-name read, its ordered child call, Forwarded at `q`, and the same physical-view origin. It asserts no mass decrease. `SourceRecursiveIntersectionEnvironment.enter_lookup/entered_bindings` identify newly entered bindings with the exact encountered Mu payloads. `Domain.lookup_complete` supplies an available Mu for older bindings. They do not attach those bindings to an INITIAL source occurrence or the selected outer ancestry.

A source renewal argument therefore also needs a binding-ancestry invariant: each live domain binding carries its causal Mu operand/source occurrence; `enter` adds the exact two current bindings, fallback preserves older bindings, reset clears the free environment, and a reference read reuses that certificate as a backedge. Warm lookup must preserve the exact request/domain. This is a separate missing invariant, not a new generic numeric rank premise.

Even these local bridges would not prove global completion. `SelectedRenewalBoundary.selected_competing_continuation` checks that the next positive child can come from the competing slot, so the selected original's positional anchor need not descend. `OuterUntouchedProgress.dispatch/budget` retain their explicit untouched-slot hypotheses. A global producer must compose competing source anchors, reference backedges, and renewed inherited constraints. No bound, infinite run, all-depth guarded-language correspondence, or Haskell defect is established by this audit.
