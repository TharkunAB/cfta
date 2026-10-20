# Next indexed original-source binder resumption

Design only. Written on 2026-10-20 at 23:01 CEST. This package adds zero Lean runs and zero proof pairs. No theorem proposed below is checked. Earlier helper and review packages remain frozen.

## Recommendation

Add one actual-build producer, provisionally `build_row_resumptions`. It should retain the ONE path returned by `NativeOriginalPublicationTrace.build_trace_writers`, select enclosing writers from that path, and derive a strictly earlier writer for a binder terminal of the SAME callback row. The first useful version can stop at stored-body `RowAt`; it need not duplicate the large universal actual-unfold interface.

The irreducible proof step is small: a terminal binder's exact selected full cell is already present at the enclosing publication's `afterBody`. Apply the common trace's precompletion clause there. Keep that exact earlier index/event and derive its raw callback source directly. This replaces an independently selected final-heap writer with a writer known to be strictly earlier in the common original-source trace.

## Existing APIs and the remaining correlation gap

The reviewed trace candidate4269eff7 has `events` at line24 and `build_trace_writers` at line462. The producer derives one `p : Path before after` from an actual completed build, Context, and explicit initialMuFree. The output supplies indexed rooted sites, final-cell writer selection, and before-completion writer selection. The final selector and precompletion selector share p. In the original-empty specialization, Context and initial Mu absence come from empty construction.

`NativeOriginalUnionDescent.of_observed` at247 fixes an enclosing event/raw callback before its all-row and all-unfold clauses. Its private `terminal_suffix` at43 constructs SourceRow and UnionDescent together. `terminal_original` at147 excludes row-bearing captures using original[]; `terminal_resume` at187 retains the same terminal five witnesses, node RowCall or binder selected payload, and actual suffix to rawAfter. The union source member indices and terminal call receipts are genuine. The public endpoint has NO membership/index clause for its enclosing event in a caller's p.

`NativeOriginalBinderResume.resume`29–71 transports the exact selected terminal payload forward to sourceHeap and calls CompletedBuildRootedWriters.build_writer. It then calls RootedMuStoredRows.of_written. This derives valid existential writers and Stored receipts but does not preserve an index in p. The event hidden in Stored is not explicitly equal to an event from an independent selector. Attaching a j to an already opaque old Observed or Stored event is therefore not justified. A common-p lookup and a separately obtained equal full payload do not prove event equality.

Choose the enclosing event from p's final-cell selector FIRST. Its exact full candidate equality aligns entry/body/Depth/ordinary with the selected sourceHeap cell. Use that event's rooted Reached and actual callback to derive the selected SourceRow and terminal. A different event with the same full payload is allowed; the theorem must expose which indexed event it uses and derive all later row receipts from that event. It must not claim equality with an earlier independently existential event.

## Exact proposed public result

Inputs are just `original`, `sourceRoot`, `sourceHeap`, and the actual equality `build original [] empty = .done sourceRoot sourceHeap`, with the existing formula/guard instances. No desired SourceRow, writer, ordinal, terminal kind, or future heap relation is a caller premise. The original-empty restriction is needed to eliminate captures and initial writer alternatives.

Return one `p : Path empty sourceHeap`, its indexed rooted-site clause, and its final full-cell selector unchanged. Then return the following universal clause for THAT SAME p:

    for every j and outer with (events p)[j]? = some outer,
      choose raw and rawAfter ONCE;
      retain exact reserved raw build, filter, Context, callback Reached;
      for every row with RowAt outer.body row,
        derive raw RowAt and SourceRow from that callback;
        choose the same terminalExpression/Inputs/Before/Raw/After together;
        retain terminal SourceRow, actual build, Context, Reached,
          exact generic SyntaxBound, UnionDescent outer.expression terminalExpression,
          physical and issued terminalAfter-to-rawAfter suffix;
        return actual node RowCall OR the binder arm below.

The node arm keeps all current distinct source/output indices and actual RowCall fields. It has no child-existence premise, so nullary rows remain covered. Do not add a value-size or generated-output decrease.

The binder arm keeps the actual CURRENT terminal Depth call, ordinary call, request, exact selected full cell, smart finish equality, and RowAt selectedStoredBody row. Append existence of i and earlier such that:

    i < j;
    (events p)[i]? = some earlier;
    Reached original [] (binder earlier.smart earlier.expression)
      earlier.environment earlier.before;
    selectedKey = earlier.key;
    selectedFullMu = earlier.candidate;
    earlier.afterBody.nodeRecords earlier.key = none;
    the same actual prefix and three callback Paths;
    Grows earlier.after outer.afterBody;
    issued extension earlier.after to outer.afterBody.

Also retain one raw callback of THAT SAME earlier event, fixed before any later row use, with its actual build/filter, Context and rooted callback Reached. For the selected row, derive RowAt earlierRaw row and SourceRow at that exact callback. Prefer a universal all-stored-rows clause at the fixed earlier raw callback if this costs only the existing deterministic raw-build alignment. This makes the earlier index/event a usable next provenance state.

The tuple must explicitly contain earlier and its index outside the raw-row quantifier. Merely appending an independently existential Stored Prop is insufficient to expose that correlation. No new generic rank/ownership predicate is needed. The notation above abbreviates existing public fields; it does not require extra public helper definitions.

A smaller private core can consume the already derived same terminal binder SourceRow and suffix, plus the precompletion selector from the once-unpacked trace producer. The public result should derive the SourceRow/UnionDescent jointly instead of asking the caller to supply desired source ancestry. The existing joint helper is private, so copy its short structural induction additively or expose an actual joint producer in the new module. Do not import generated private names. The older public terminal_source21–105 alone drops UnionDescent and cannot recover it afterward.

## Concrete proof route

1. Call build_trace_writers once at original[]/empty. Keep p and all three output clauses in scope. Indexed outer Reached comes from the same selected lookup.
2. Use PublicationCallbacks.contexts33–44 and callback_raw20–30 to fix the actual reserved raw build/filter once for outer. Derive its local Context from the actual reservation and available own reference. PublicationBodySourceRows.publication_body_origin26–67 supplies each raw row/source. If this re-exposes raw existentially per row, align it to the already fixed raw via equality of the SAME actual build, as RootedMuStoredRows.of_written does at lines49–53.
3. Reuse the additive joint SourceRow induction from UnionDescent43–184 to produce the same terminal and route. This preserves actual union take/member/drop calls. Original[] excludes capture; it does not require a false gate or native reader.
4. In the binder arm, case the SAME terminal SourceRow.binder. Its selected field is an exact full cell at terminalAfter, including stored body, Depth and ordinary. Keep its RowAt anchor. Do not substitute the current callback for a historical warm winner.
5. Context.build plus rawBuilt derive Valid at rawAfter. Apply run_correct and run_issued_extends to the SAME actual withoutSelfReference filter. This yields rawAfter-to-outer.afterBody, BEFORE completion. PublicationCallbacks.raw_callbacks47–98 already supplies the physical half. NativePublicationRawSuffix.callback_suffix17–37 proceeds to outer.after; it cannot be reversed and should not be used as the before-completion endpoint.
6. Compose the actual terminal suffix with this filter suffix. Forward the exact selected full cell to outer.afterBody. Apply the SAME p's precompletion clause for (j,outer) to that cell. Empty initial records eliminate the prior arm inside the trace theorem. This gives i<j, SAME earlier event and full payload, rooted Reached, Paths and actual physical/issued suffix.
7. Align selected full payload to earlier.candidate by Value.mu injectivity. Use PublicationBodySourceRows.publication_body_origin with earlier and its SAME rooted Reached to recover the selected stored row at earlier's actual raw callback. If all rows are exported, fix callback_raw first, then align every returned raw build by Outcome.done injectivity. Do not search for another writer via BinderResume.resume/build_writer or unwrap another Stored and assert event equality.

## What this controls and what remains missing

This would make a binder-resumption chain within ONE completed original source build decrease in natural publication index. It handles warm winners without proving source-writer uniqueness. The current terminal expression and the earlier winner expression can differ; i<j carries the chronology across that jump. UnionDescent controls only the source union route into the current terminal and does not identify the earlier writer's source expression. Nullary RowAt needs no child lookup.

This is still an unproved local source-ancestry producer. No existing public endpoint currently appends i<j and a fixed earlier callback to the same union terminal tuple. The required arithmetic/order foundation is now checked; the before-completion cell transport and indexed row-facing correlation are the next implementation work.

To connect an actual initial native capture, OriginalCapturedMuRows.capture_source39 onward already returns the exact initial full cell at the heap that equals the actual original build return. Feed THAT cell to p's final-cell selector. Do not preserve the old Observed hidden event by unsupported equality. Actual unfold consumers can use CapturedMuUnfoldRows.unfold_rows79–121 to get RowAt of the SAME selected stored body under explicit current SemanticHeap, Available and causal publication History. This plan does not infer earlier causal history by reverse growth.

Node child descent still requires the actual ordered child/source route. IndexedRowCallChildren.indexed_child57 onward gives the exact source child call and generic structural syntax bound. It does not by itself locate all later generated captures in this original source trace. Proper union descent, child-syntax bounds, and publication order do not automatically constitute one verified global native progress relation.

The later-created generated encode case has a different root and a nonempty captured leaf pool. The original[]/initialMuFree specialization does not cover it. Existing chronological native-prefix capture results stay separate. Further work must relate node captures, warm generated winners, current native owner renewal, and repeated/residual Mu observations to an actual well-founded global measure. No native runtime termination, strict value decrease, original lexical uniqueness, or Haskell refinement is claimed here.

## Files and verification

plan-source-pins.json records exact whole-file ROOT inputs and the frozen reviewed trace candidate. inputs/ contains portable ROOT snapshots; candidate/ contains the exact517-line trace source4269eff7. Run plan-verify.py --root ROOT from any directory. Add --live to compare ROOT files and, once installed, the official trace source. No verifier invokes Lean. The manifest excludes itself and the generated verification receipt.
