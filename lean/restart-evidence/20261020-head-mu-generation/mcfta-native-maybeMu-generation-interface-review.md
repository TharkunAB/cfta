# Native maybeMu generation: next exact producer

Read-only source audit at 2026-10-20 17:35 CEST. No production source, repository file, Lean artifact or earlier evidence was changed. No Lean job or proof pair was run. The proposed heads below are design targets, not newly checked theorems.

## Existing endpoints do not cover every physical cache cell

`SourceCurrentNativeMuBodyOrigins.Body`, lines 35–50, retains one actual Mu compiler interval. It records the captured request's identities, entered domain, exact open child request and Trace, checked child entry and middle, available parent bodyValue, the actual maybeMu call at middle, and the final physical advance. The maybeMu ENTRY is middle.native.machine.heap. It is not the captured query's earlier entry heap or the final reader.

`Body.trace` can recover that interval from an actual completed compileMu Trace, Good before, final native History and Retained. `Body.returned` and `Body.request` recover it from a returned native request. They do not classify every full Mu in the physical heap.

`NativeMuWriterSourceRows.returned_mu`, lines 86–104, additionally requires a selected nodeEdges row of the returned request value. Its anchor is in the actual generated parent bodyValue. `NativeMuSourceHandoff.returned`, lines 72–124, retains that same captured writer and either literal child provenance or a first opaque Mu's publication. Neither endpoint takes an arbitrary selected full Mu cell in the later physical cache. Probe-only and nested publications need not be the returned native value or an ordinary row in it. A selected Mu may also be installed before an enclosing native owner finishes. The returned-cell endpoints cannot be used to assume that owner's return.

## Minimal operation-local extraction

The local helper should take the actual `maybeMu pair parentBody middleHeap = done optionalResult heap`, the semantic heap and parentBody availability at middleHeap, and an ARBITRARY full Mu selected in heap.nodeRecords. Its result should be the exact same full cell at middleHeap, or ONE same selected first-write event rooted in this operation's actual generated source build.

If the pair name is absent from parentBody.free, maybeMu returns parentBody with the identical heap. Only the entry-cell arm is possible. If it is present, `SourceRecursiveIntersectionMaybeMu.construct_eq`, lines 48–56, identifies the entire operation with:

`build (binder true (encode (leaves parentBody) [oldPair] parentBody)) (leaves parentBody) middleHeap`.

This includes its probes, reservations, nested source binders, selected warm cells and smart finish. Build the rich joint Context at that SAME entry from `SourceRecursiveIntersectionSemanticHeap.context`, `leaves_available` and the semantic depth heap, as the existing private `NativeMuHistory.context` does. Then `CompletedBuildRootedWriters.build_writer_or_prior` supplies the exact entry-cell alternative or a rooted Written receipt for any selected cell. No RowAt, nodeEdges, returned-value identity or desired ancestry premise is needed.

Keep the generated root, initial leaves and parentBody in the same result as the selected event. Retain full key and candidate equality, first-write absence, event Reached, the entry-to-event issued Path, all three actual callback Paths, and physical plus issued growth from event.after to the operation return. The chosen event can occur inside a probe or nested encoded binder. It is not necessarily the operation's outer binder publication. Do not identify its stored body with parentBody or its expression with a current warm requester.

This helper alone is not the missing chronological generation producer. Its exact entry-cell arm must be followed through earlier actual execution rather than labelled as a publication of the current parentBody.

## Recommended substantive head: selected generation in actual native execution

Use a head such as `request_selected_generation`: actual completed requestNode Trace, initial Good, and an arbitrary selected complete physical Mu at its return. Return the exact initial full cell OR a generating operation site and the SAME rooted first-write event from the local helper. Do not require a supplied writer, original-root certificate, semantic comparison law, selected result row, or future outer return.

The operation branch must retain these data together:

- Exact checked prefix and suffix Trace intervals locating the optionalBinder instruction, its continuation and actual physical advance. Retain the actual bodyValue at this instruction's ENTRY and its availability there.
- The actual captured Mu request and compileMu interval, identities, entered domain, open body request, its checked entry, exact child Trace and middle state. The optionalBinder entry must equal this actual middle as data, not by equality of Prop proofs.
- The literal maybeMu equation, exact generated source root and initial leaf list, and the selected publication's complete payload, rooted route and issued intervals.
- Actual physical and issued suffixes into the final heap. Keep native Retained separately when retaining child memo provenance. A memo handle or Forwarded receipt must come from the actual native call/history, not from physical heap growth.

A generic Trace induction can first locate an optionalBinder site for every cell absent initially. `NativePublicationTrace.work_noNewMu`, lines 22–29, excludes new Mu from all physically admitted primitive Work jobs. Other native instructions preserve the heap; `NativePublicationTrace.step`, lines 64–103, already enumerates the cases. The optionalBinder case applies the local helper. When that helper returns an entry cell, continue into the earlier prefix. Derive Good, semantic state, Keeps and native Retained from actual prefix/suffix effects where needed. Do not try to factor an arbitrary publication History backwards.

However, a generic Trace can start with caller-written optionalBinder code. Locating that instruction alone does NOT prove a captured compileMu owner. For the recommended requestNode head, attach the owner by induction through actual compiled request, edge and ordered-walk traces. Use actual lookup/demand captures, `after_step` and `bind_inverse`; recurse on the smaller actual child Trace. `compileMu` has exactly enter, the open body request, and optionalBinder. The existing `NativeMuWriterOrigins.trace` supplies its exact completed schedule without an internal History assumption. Retain an earlier captured request if a memo dispatch uses it; do not silently replace it with requester syntax. This owner attachment is a real remaining proof step, not already supplied by the generic site locator.

## Chronology and stopping-outcome limits

Native memo `EdgeWriterGrowth.History`, lines 277–289, is not sufficient by itself. Its initial machine is arbitrary, and its advance constructor accepts only physical Grows. Such an advance may contain a Mu added by a different operation. Neither that constructor nor a bare publication History records the native generating instruction. The actual checked trace or another explicit operation-labelled history must be retained.

The yielded Trace target above covers every physical cell in that trace, including cells unrelated to its returned value. It does not cover the heap effects of a final blocked optionalBinder instruction. `SourceRecursiveIntersectionNative.step`, lines 48–51, advances the heap even when maybeMu returns pending. Its already completed nested publications must not be discarded.

For an all-outcome execute endpoint, extend rooted selected-writer extraction to `build expression inputs before` at Outcome.state, including pending. `CompletedBuildRootedWriters` already constructs a private stopping `build_supported` path and its writer induction handles every issued Path; the public build_writer_or_prior currently requires done. An additive stopping-outcome endpoint can expose that existing support without a completion premise. Combine it with the used-branch maybeMu_eq and the literal terminal native step. `NativePublicationTrace.execute` already preserves semantic heaps and publication History on blocked and failed outcomes, but does not preserve the operation labels or issued Paths needed here.

The final producer must state which of these two scopes it proves. It must preserve the exact initial complete-cell alternative. It must not claim original program ancestry, a full-self decrease, native-reader History transport, guarded semantic equivalence, renewal or termination. No concrete Haskell defect or checked counterexample is claimed by this audit.
