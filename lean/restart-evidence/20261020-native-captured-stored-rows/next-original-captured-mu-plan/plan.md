# Next original-source attachment for a captured initial Mu

Design review on 2026-10-20 at 21:21 CEST. Proposed and unproved. No Lean job or production edit belongs to this report.

The next substantive producer should close the exact initial-cell arm of NativeCapturedMuUnfoldRows.capture when the native entry heap is exactly the output of an actual source build from empty. It should retain the existing generated arm unchanged. It should not add another generic availability or query-scope wrapper.

The minimum new input is:

```lean
built : InternedFreshOrdinaryConstruction.build original [] empty =
  .done root before.native.machine.heap
```

Keep the current actual root request Trace, initial Good and native writer History, reached optional body Available, and exact indexed full-Mu leaf lookup. The source build derives initial SemanticHeap and causal publication History internally. It does not derive native memo History at an arbitrary reader.

The proposed sole actual consumer is capture_source. Its initial result is:

```lean
before.native.machine.heap.nodeRecords entry.key =
    some (.mu entry body depth ordinary) ∧
SourceCurrentNativeCapturedMuUnfoldRows.Observed
  original [] empty before.native.machine.heap
  entry.key entry body depth ordinary current.native.machine.heap
```

Its other result is the exact existing generated existential from NativeCapturedMuUnfoldRows.capture, including the same earlier optional operation, generated encode root, rooted Written, terminal Origin, Stored and Observed witnesses. This phrase is specification shorthand for that existing public result type. It is not a new assumed Generated predicate or a source ancestry premise.

Observed already includes the complete Stored and Written event fields. It chooses the publication and raw callback before all stored rows and all actual successful unfolds. The initial result therefore does not need separate unrelated existential Written, Stored and Observed conjuncts. The full Mu payload, key, event, Context, original source Reached, exact callback build/filter, physical intervals and issued intervals remain inside one Observed receipt.

The direct proof route is as follows.

1. Derive initial SemanticHeap with SourceRecursiveIntersectionSemanticHeap.constructed from built. Derive causal publication History with NativeMuPublication.closed_history original and rewrite the actual completed build state. Keep initial native writer History explicit.
2. Invoke NativeCapturedMuUnfoldRows.capture once on the same actual indexed captured Mu. Return its generated arm unchanged.
3. In its exact initial-cell arm, call CompletedBuildRootedWriters.build_writer with original, empty initial inputs, empty source heap, empty_context, built and that exact full-cell equality. Literal emptiness of the initial nodeRecords proves initialMuFree. This yields Written original [] empty before.heap entry.key for the same full Mu. Availability in the source heap is not needed for this step. The initial-cell equality is already the required exact selection.
4. Convert that same Written to Stored while fixing the event and raw callback before the universal row field.
5. Derive current SemanticHeap and causal publication History with PublicationTrace.from_history along the same actual native prefix. Derive current Mu Available with leaves_available from the reached optional body's Available and the exact indexed leaf lookup. Apply NativeCapturedMuUnfoldRows.observe to the same Stored witness and those actual current facts. No Ready, reader native History, current query completion or future successful unfold is an input.

OriginalRequestScope.available_writer already proves the source-build-to-Written fact for an available full Mu, but it is private and is called only inside queried NodeScope attachment. The next consumer does not need to expose or duplicate it. The initial-cell branch gives a stronger exact selected-record equation directly, and public CompletedBuildRootedWriters.build_writer already consumes it.

The only public API gap is the general Written-to-Stored conversion. NativeCapturedMuStoredRows.stored already proves it, but it is private. The minimal nonduplicating public type is:

```lean
of_written
  (written : Written root initial before reader key
    (.mu entry body depth ordinary)) :
  Stored root initial before reader key entry body depth ordinary
```

The current goal already authorizes the necessary proof work. Preserve the published frozen module bytes. Use a new additive public of_written adapter that reconstructs the same fixed-event argument from the existing public callbacks.contexts, callback_raw, Reached.enter and PublicationBodySourceRows.publication_body_origin producers. An external additive module cannot access the existing private stored proof through a normal public API. Do not use generated private names. The approximately 40-line adapter duplication is an explicit cost of that access boundary. Then implement one actual capture_source consumer as specified above. Add no new framework. No user permission is required. This route is settled, but this report implements no proof and runs no Lean job.

The fixed-event part must remain outside the row quantifier. Unpack Written once, retain the exact event and full payload equalities, obtain one actual raw callback, and then prove every RowAt body row using publication_body_origin on that same event. Its returned callback is aligned with the fixed one by equality of the same actual completed build. Calling written_body_origin independently under each row quantifier would give weaker public witness correlation and should not replace the fixed event/raw receipt.

The source-root distinction is material. In the initial arm the root is original and the initial capture list is empty. The selected writer comes from that exact original source execution. It does not assert a unique lexical binder occurrence or identify the current requester with the earlier winning writer. Its actual Reached field supplies the original-root Path and callback crossings. SourceCaptureOriginalSlots.empty_initial can then exclude a row-bearing captured variable along a supplied Path from that same original root.

The generated arm has a different root: binder true of encode(leaves parent) with the pair-local reference, and its initial captures are leaves parent. Those captures can be nonempty closed ordinary values or Mu values. Empty-initial capture elimination does not apply there. NativeSelfCaptureSlots gives only exact closed-leaf identity or complete-self-Mu replacement for an actual mapped stored-unfold slot. It does not attach an arbitrary optional-generated closed capture to original program syntax. An occurrence lookup also does not establish the canonical encode.slot index or unique source occurrence.

The exact entry-heap equality must remain in the proposed theorem. A weaker Grows from the original source heap into a later query entry heap does not justify moving a selected full record backward. A Head/read/unfold operation or earlier native interval may have introduced that Mu after the source build. Those cases need their actual first-generation interval and generated writer, not the source build writer for a cell absent from its output. Existing HeadMuGeneration handles the Head stored-unfold operation family; native optional generation handles its own actual family. Combining them across arbitrary outer intervals and all root-entry cases remains separate work.

Observed covers literal rows after a successful unfold and maps them to full stored RowAt rows and the fixed raw callback SourceRow. RowAt can traverse union and stored Mu syntax, but it does not itself prove an observed epsilon read through another Mu or descend through ordinary children. Residual Mu observations and ordinary-child continuation ancestry need their actual read/unfold or indexed child receipts. They are not supplied by a structural row occurrence.

Finally, strict earlier-prefix fuel in the generated arm is a local historical decrease inside the supplied finite Trace. It is not a future runtime rank or a decreasing measure across arbitrary warm writer selections. Original-program renewal for general generated captures, prior Head/native entry intervals, full residual observations and global busy-owner exclusion or termination remain open after capture_source. No Haskell or runtime defect is claimed.

Source authority reviewed: e9d4bbcc432d0f6862a3bc8e4a2579a38a9ea94e. Exact relevant live source bytes are pinned in the companion portable plan package. No theorem from this plan has been implemented or checked.
