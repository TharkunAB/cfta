# Next common-trace publication order for original binder resumption

Design only. No theorem in this note has been implemented or checked.
Written 2026-10-20 22:39 CEST. This package adds zero Lean jobs and zero proof pairs. Frozen predecessors remain unchanged.

## Result of the source audit

A resumed terminal's exact selected full Mu can be shown to exist BEFORE the enclosing selected publication completes. This is derivable from current actual receipts; no reverse growth or source-writer uniqueness is needed. Public issued paths then recover an earlier causal writer whose actual return grows to that before-completion heap.

The stronger iterative original-source order needs one common finite rooted build trace. Current public Written and Stored erase membership in that common trace. A separately recovered source-rooted writer cannot silently replace the earlier writer from the before-completion prefix. Therefore the primary proposed next producer returns a shared rooted trace and selected event positions, rather than another conjunction of independent writer existentials.

## Existing local derivation: a private ingredient

Take the SAME enclosing event/raw/rawAfter and its prefix/depth/ordinary/body issued paths from the current fixed Stored/Observed receipt. Take the SAME resumed terminal binder SourceRow, actual selected key/full payload at terminalAfter, and derived terminalAfter→rawAfter physical/issued suffix.

1. Context.build and the actual raw build derive rich Context and Valid at rawAfter. Apply run_correct and run_issued_extends to the SAME actual filter equation. This gives rawAfter→outer.afterBody, stopping BEFORE completion. NativePublicationRawSuffix.callback_suffix currently continues to outer.after; use only its first actual-filter argument here.
2. Compose terminalAfter→rawAfter→outer.afterBody. Forward the SAME selected nodeRecords cell. Keep its entry, stored body, Depth and ordinary fields unchanged. No RowAt child is required, so nullary anchors remain covered.
3. The selected enclosing writer receipt includes outer.afterBody.nodeRecords outer.key=none. The transported selected full cell therefore has key≠outer.key. This is a physical first-write distinction; it is not a source-size decrease.
4. Assemble Path empty outer.afterBody from the exact prefix to outer.before, outer depth path, outer ordinary path, literal reservation retain, and outer body path. Reservation changes only nodes. Use public reserve_growth and intern_issued_extends with the actual cut Context; do not infer issued growth from Grows. These are precisely the constructors used in MuIssuedHistory115–137 and MuIssuedWriters73–95.
5. Public MuIssuedWriters.from_empty (108–116) applied at outer.afterBody supplies an actual earlier event for that SAME key/full payload, with its callback paths, missing-before-write fact, and physical plus issued suffix from earlier.after to outer.afterBody. No Ready or successful replay is needed.

This derivation gives actual source-callback chronology. It does NOT by itself give Reached original[] for that newly chosen earlier event: public Path has no original-root annotation. Nor does it equate that event with the event hidden in the existing independently existential source-rooted Written/Stored at sourceHeap. Keep these distinctions explicit. Do not publish this local ingredient as if that correlation gap were solved.

## Why existing public endpoints do not yet close iterative order

MuIssuedHistory.Path is a finite Type with refl, retain, trans and publication, and each publication contains its three actual callback paths (26–39). MuIssuedWriters.writers/from_empty preserves the SAME recovered event and the correct suffix, but returns no position of it in the supplied path. MuPublication.History alone also loses growth/issued suffixes; its writer cannot upgrade these from history alone.

CompletedBuildRootedWriters has the needed correlated rooted support PRIVATELY: Rooted and Supported (39–51), actual build_supported (145 onward), and writers (280–331). The public actual build_writer (349–362) returns only the chosen event's root Reached and local paths/suffixes. It discards the encompassing path, its Rooted proof and chosen occurrence. StoppingBuildRootedWriters has the same private correlation discipline. Arbitrary Path plus a separately obtained source-rooted writer cannot recover it. Private generated declaration names must not be imported.

A chronological path cannot in general be factored into a Path for a standalone completion step afterBody→after: Path.publication starts BEFORE the callbacks and packages them with completion. Use its finite tree/chronological event list and genuine physical/issued suffixes. Do not invent an issued suffix Path merely from growth.

## Smallest useful common receipt and exact proposed API

Propose one generic public chronological list function on issued Path:

    events(refl) = []
    events(retain) = []
    events(trans first next) = events(first) ++ events(next)
    events(publication event depth ordinary body) =
      events(depth) ++ events(ordinary) ++ events(body) ++ [event]

This postorder is actual callback/publication order, not syntax-tree order or reservation identity order. Every path is finite. The index is relative to this ONE chosen path. Reflexive/retained subdivisions do not add events. No cross-path uniqueness is needed.

Propose one additive actual-build producer, schematically build_trace_writers:

    Context before initial
    build original initial before = done sourceRoot sourceHeap
    initialMuFree before
      -> exists p : Path before sourceHeap,
          (forall j outer, (events p)[j]? = some outer ->
             Reached original initial (binder outer.smart outer.expression)
               outer.environment outer.before) and
          final_selected_writers(p) and
          precompletion_selected_writers(p)

The actual closed specialization uses before=empty and initial=[]; it derives empty Context and initial Mu absence. Neither p nor its rooted sites nor a desired writer is a user premise. Derive them together through the existing actual source build recursion. This is the same substantive joint-support proof as the frozen private implementation, exposed additively with event positions. Keep any generic helper implementation private unless a real consumer requires it.

Here final_selected_writers(p) means: for EVERY selected final full Mu cell, return j and outer from that SAME events(p), exact selected key=outer.key and full payload=outer.candidate, outer.afterBody missing, original Reached from that occurrence, all existing prefix/callback issued paths, and Grows/issued outer.after→sourceHeap. If a nonempty initial table is supported, retain the exact initial-cell arm; the closed specialization removes it.

Here precompletion_selected_writers(p) means: for EVERY j/outer with `(events p)[j]?=some outer`, and EVERY full cell present in outer.afterBody, return i/earlier such that i<j, `(events p)[i]?=some earlier`, exact key/full candidate equality, earlier.afterBody missing, the existing earlier prefix/callback paths, and Grows/issued earlier.after→outer.afterBody. With nonempty initial tables, retain the exact initial-cell arm. Rooted source Reached for earlier comes from the SAME p's indexed-site clause. The empty-table case has no initial alternative.

These clauses share one p. They are NOT independent existential Written/Stored events. Keep the SAME chosen earlier event, its index, root Reached and callback receipts in one output tuple. A later fixed-event raw-row conversion can use PublicationBodySourceRows.publication_body_origin directly with that event and its rooted Reached. It must not invoke an independent writer search and assume event equality.

This API is two public heads in the minimal design: events and the actual producer. The displayed notation and all new clauses are unproved. A private ordered-writers induction can extend the existing writers proof, retaining list positions through trans and callback-list offsets. At a selected first write, the occurrence is the final event of that publication subtree. At an earlier cell, descend into the relevant actual callback/prefix path. NoNewMu retain returns the prior alternative; it cannot introduce a selected event.

## How this advances finite source ancestry

The initial final-cell selection chooses its writer occurrence j in the actual original build trace once. Its raw callback/source-row traversal and binder resumption show that a selected inner full cell is present before that occurrence's completion. The SAME trace's precompletion clause chooses its earlier writer at i<j. Carry THAT event/index and its fixed raw callback forward as the next source provenance state. The universal indexed-site/precompletion clauses remain available at every earlier position of that SAME finite p, so this local original-writer resumption chain is well founded by natural event index.

Do not use cache reservation identity or nodes.next as this order. An inner Mu can be reserved during an enclosing reserved callback and receive a larger identity while still publishing before the enclosing completion. Count actual publication events in the finite trace instead.

If the implementation stops after the private before-completion ingredient, state the remaining gap exactly: source-rooted Reached and common-path occurrence for its selected earlier writer are not yet exported/derived. Existing arbitrary public Path does not supply that annotation. The proposed shared actual-build producer is the concrete next useful ancestry step; an uncorrelated rank wrapper is insufficient.

## Scope boundary

This is source-publication chronology. It is not a general native owner-renewal rank. Native generated encode roots, original cache owners versus later-created captures, current/requested callbacks versus warm stored winners, source-node child descent, and repeated/residual Mu observations still need their own actual correspondence. A finite already-completed source build does not bound how many new native calls a future execution creates. No original lexical occurrence uniqueness, strict syntax inequality, runtime termination, or Haskell refinement is claimed.
