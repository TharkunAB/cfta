# Stopping-build rooted writers: additive API and proof plan

Read-only design audit at 2026-10-20 17:42 CEST. No Lean code, Lean job, candidate, repository file or frozen evidence was changed. This plan uses public declarations only. It must not invoke generated `_private` names or change SourceCurrentCompletedBuildRootedWriters.

## Exact requested API

Use a new namespace such as SourceCurrentStoppingBuildRootedWriters and one public head, build_writer_or_prior. Its inputs should be the original root Syntax, initial lexical values, entry heap, joint Context at that entry, the selected key and complete Mu fields, and an exact selected equation at `(InternedFreshOrdinaryConstruction.build root initial before).state`.

Return the exact same complete cell in before.nodeRecords OR the EXISTING public `SourceCurrentCompletedBuildRootedWriters.Written root initial before stopped key fullMu`, where stopped is that Outcome.state. Reuse this Written type so written_body_origin and later consumers need no adapter. Keep the complete payload equality, rooted event Reached, first-write absence, actual entry/event/callback issued Paths, and physical plus issued suffix inside the same Written witness.

The selected equation is about every full Mu cell at the stopping heap. It does not require that the source result is that Mu, that a row is selected, that the source completes, or that the caller supplies an event, writer, ancestry or later completion. Consumers can rewrite an actual done or pending equation into the head. A separate public pending-only head or public support type is unnecessary unless a consumer needs it.

## What already works without copying the rooted proof

`SourceCurrentNativeMuIssuedHistory.build_path` produces an issued Path from entry to the actual build's Outcome.state for both done and pending. `SourceCurrentNativeMuIssuedWriters.writers` then derives the exact initial complete-cell alternative or a selected unrooted Written receipt, preserving one event and all issued intervals. This stopping UNROOTED endpoint needs approximately 10–15 lines, not the old support proof. It is useful if the immediate consumer needs only physical chronological publication provenance.

It does not give Reached under the actual source root. Its Path has publication and causal fields but no source-root annotation. Adding an actual publication History does not add that annotation. The public generic heap inductions likewise receive actual events but no original-root Reached fact. Two independently obtained event existentials cannot be identified merely because they publish the same selected payload. Thus the unrooted endpoint must not be called rooted or treated as a complete solution to this task.

The old module's private source support construction carries the missing source label through each actual callback and sibling. Merely forgetting it and later applying public writers does not restore it. Its private support and selected-writer spans cover 286 source lines, including comments and blanks: 39–72, 74–141, 145–253 and 257–331. Reconstructing that architecture additively would duplicate about 280–300 lines. The public completed endpoint is at lines 334–346.

## Smaller reuse-oriented route: pending completed-subcall extraction

Split the requested proof on the actual build outcome. In the done branch, directly apply the existing public build_writer_or_prior. Only the pending branch needs new source-schedule reasoning.

First split on whether the complete selected cell was already present at the original entry. If it was, return the exact initial arm. Otherwise prove a private pending-prefix lemma. It should derive one ALREADY COMPLETED actual source subcall and retain:

- Its source expression, exact lexical values, entry heap, returned value and return heap.
- Joint Context and Reached under the original root at that entry.
- Its exact completed Fresh build equation.
- The selected SAME complete Mu at its return, and absence of that complete cell at its entry. Non-equality to `some fullMu` is sufficient; no stronger none premise is needed.
- An actual issued Path from the original entry to this subcall entry, plus physical Grows and issued Extends from this subcall return to the pending stop.

This is a producer from the actual pending schedule, not a supplied completed-subcall assumption. A new Mu can be installed only by the completed reserved-body publication step. A pending source computation has not performed its own final completion. Every new selected cell already came from a completed earlier subcall, possibly inside a probe or another pending callback. The returned value of that completed subcall can be unrelated to the selected Mu.

For pending node and union calls, the ordinary final Work cannot be pending. Follow the actual pending buildEdges or buildMany call. For ordered lists, a pending head recurses into that head. If a head completes and the tail is pending, inspect the exact full cell at the head return. If present there but absent at the list entry, the completed head supplies the witness. If absent there, recurse into the pending tail. Actual contexts and earlier issued Paths retain Reached and prefix chronology. Edges add a no-new-Mu makeEdge interval between the completed child list and later rows. This route also covers dead source rows and discarded results.

For a pending binder, split its literal Depth, ordinary and reserved-body schedules. A callback can be pending only because its raw source build is pending; the root filter is always an Outcome.done Work step. Recurse into that raw build with the actual Entered crossing, available local reference and joint Context. For completed earlier callbacks, use their actual raw build and filter. filter_noNewMu moves a selected full cell backwards across the filter; actual run growth and issued extension supply its forward suffix. A pending cache hit at cut publishes nothing. A fresh reservation leaves nodeRecords unchanged, so move any already-present cell backwards across that reservation before considering the earlier completed probes. A pending fresh body recurses into its actual raw source body. Never assume that the missing outer payload has been completed.

The private recursion needs expression, child-list and edge-list cases, as the executable schedule does. It can reuse public build_path/buildMany_path/buildEdges_path for actual issued intervals, build_verified for physical and issued growth, Context.build/many/edges/callback/reserve/local, Reached.node/union/enter/grows and Crossing/Entered. It need not recreate a Rooted predicate on every publication Path or reprove generic selected-writer induction.

## Reuse the completed writer while retaining the SAME event

Apply the public completed build_writer_or_prior to the produced completed subcall. Its initial arm contradicts that subcall's derived absence. Its writer is rooted in the subcall expression and input list.

Re-root that SAME writer to the original root with a small private composition lemma. Unpack the original Reached path to the subcall and the writer's inner Reached path to its binder. `InternedFreshOrdinaryActiveOrigins.Path.trans`, lines 104–114, combines the paths with inner crossings followed by outer crossings. The writer's actual prefix Path.growth advances every outer crossing from the subcall entry to event.before. The inner Reached already supplies growth for its own crossings. This derives the original-root Reached for that exact event.

Prepend the produced original-entry-to-subcall issued Path to the writer's event prefix. Compose its event-to-subcall-return physical and issued suffix with the produced subcall-return-to-pending-stop suffix. Unpack and repack the public Written tuple; the old private prepend/later helpers need not be accessed. These operations preserve the same event, payload and all callback Paths.

This plan is estimated at 200–300 new proof lines, including pending source/list/binder geometry and roughly 30–50 lines for same-event path re-rooting and interval adapters. It has not been elaborated, so a smaller total is not guaranteed. Its advantage is semantic reuse of the completed selected-writer theorem rather than copying the old approximately 286-line support/selection architecture. No current public lemma removes the pending source-schedule obligation entirely.

## maybeMu and native scope

At an actual maybeMu entry, SemanticHeap and parentBody availability derive the joint Context for leaves parentBody. In the used branch, maybeMu_eq identifies the entire stopping outcome with the generated binder build. The new stopping head can then select any full Mu in its resulting heap, including nested publications before a pending outer constructor. In the unused branch the heap is unchanged and only the entry-cell alternative is needed.

This closes only stopping SOURCE-build writer extraction. Recovering the actual native optionalBinder instruction and attaching its same captured compileMu request, entered domain and body query remain separate producers. A successful yielded Trace-only producer may be an interim result, but it must not claim the final blocked instruction's partial heap effects. Generic native memo History advances still do not supply operation generation labels or issued intervals.

No original-root ancestry for native mapped captures, complete-self decrease, observation transport, renewal, termination or Haskell refinement follows from this plan. The initial complete-cell alternative remains exact.
