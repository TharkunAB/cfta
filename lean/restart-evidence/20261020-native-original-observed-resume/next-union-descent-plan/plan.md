# Next correlated union-only terminal descent producer

Design only. No theorem in this note has been implemented or checked.
Written 2026-10-20 22:23 CEST. This package adds zero Lean jobs and zero proof pairs. Existing frozen sources remain unchanged.

## Exact missing fact and smallest addition

Current OriginalObservedResume retains the SAME five terminal witnesses and actual terminal SourceRow/build/Context/Reached/suffix, then adds a node row call or a binder resume. It does not state that the terminal expression follows from the fixed enclosing callback expression by only original source-union members. Global Reached and the generic size bound cannot supply that fact: an earlier reached node callback can also produce the same row.

The smallest sufficient addition is one pure generic predicate plus one additive observed consumer. A proof-indexed route or a second execution hierarchy is not needed for the present branch-forcing target.

Proposed predicate, in schematic Lean notation:

    inductive UnionDescent : Syntax Symbol Guard -> Syntax Symbol Guard -> Prop
    | refl (expression) : UnionDescent expression expression
    | member {members member terminal} {index : Nat}
        (selected : members[index]? = some member)
        (nested : UnionDescent member terminal) :
        UnionDescent (Syntax.union members) terminal

Declare it generically, before native aliases. It needs no heap, row, semantic relation, DecidableEq, future execution, or source-rank premise. It follows source Syntax.union only. It does not descend node children, a variable capture, a stored Mu, or a binder callback. A binder is a terminal for this relation; its historical selected-writer resumption remains a separate branch result.

Keep UnionDescent expression terminalExpression inside the SAME terminal existential as the five actual terminal witnesses. Do not add an independent existential descent target beside the old Terminal. The pure predicate alone does not identify a unique intermediate occurrence or execution. Existing SourceRow receipts and the producer's joint construction supply the actual calls. In each union induction case use the original member index and selected equation from that SAME SourceRow.union constructor. Do not use a stored-value union prefix or an encode.slot index.

## Private generic producer

Adapt the existing terminal_source SourceRow induction additively, without changing its frozen source. The helper can remain private. Its schematic result is:

    Context before inputs -> Reached root initial expression inputs before ->
    SourceRow expression inputs before raw after row ->
    exists terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row and
      UnionDescent expression terminalExpression and
      nonunion terminalExpression and Context terminalBefore terminalInputs and
      Reached root initial terminalExpression terminalInputs terminalBefore and
      genericSyntaxBound terminalExpression expression and
      Grows terminalAfter after and issuedExtension terminalAfter after

All terminal witnesses and the full selected row stay shared across this conjunction. The helper derives the actual completed terminal build from that SAME SourceRow as the current original terminal producer does. The displayed notation is a proposal, not checked Lean.

For capture/node/binder, stop at the exact input receipt and add UnionDescent.refl. Preserve its actual heaps and full row; do not inspect a binder's selected stored body to continue this source-union traversal. For SourceRow.union, recurse on its actual nested SourceRow once. Add UnionDescent.member using its original source index and lookup. Reuse the current actual earlier buildMany growth for Reached, actual member return Context, actual suffix buildMany and literal makeUnion growth/issued equations. Compose the existing terminal suffix with those same effects. Preserve the generic syntax measure selected before native aliases.

Original initial[] then excludes a capture terminal with SourceCaptureOriginalSlots.empty_initial on the SAME terminal Reached/capture lookup. This gives node-or-binder without assuming a false gate or a desired terminal kind. There is no child-existence premise; nullary RowAt remains covered.

## One additive of_observed consumer

Inputs remain exactly the current actual build and base Observed:

    build original [] empty = .done sourceRoot sourceHeap
    Observed original [] empty sourceHeap key entry body depth ordinary current

Unpack base Observed once. Keep its SAME enclosing publication event and raw/rawAfter outside both universal clauses. Carry all original payload equalities, missing-cell fact, issued paths, callback build/filter, Context/Reached, physical/issued suffixes and actual-unfold support unchanged.

For each stored row, consume its existing RowAt/raw SourceRow once. Run the private joint descent producer on that actual callback SourceRow. Retain its SAME five terminal witnesses, append UnionDescent event.expression terminalExpression, then case the node-or-binder kind. In the node arm invert that exact SourceRow to expose the existing canonical output index, distinct original source index, complete RowCall and call.output=row. In the binder arm call OriginalBinderResume.resume once for that exact terminal SourceRow and suffix, with the fixed enclosing callback receipts. Preserve its entire selected-payload/probe/request/finish/growth/Written/Stored result.

For every actual successful unfold, retain the original stored anchor originalRow, full symbol/guard/arity correspondence, actual identity-or-Calls, and output support/history. Construct descent and resumption for that SAME originalRow. Do not replace it by the changed output row or equate their children.

The result is the current complete observed-resume receipt with just the correlated UnionDescent conjunct under each terminal existential. Generic SyntaxBound can be reused from the current public module. No extra public transport framework is required.

Important limitation: an arbitrary old Terminal or current extended terminal does not imply this new descent. Do not call the old terminal theorem and attach descent afterward to opaque witnesses. The additive proof must derive terminal and descent together from the SAME original callback SourceRow. It can then forget the new conjunct to recover the old receipt shape. It need not equal a previously chosen existential terminal from a different theorem application.

## Proposed honest binder fixture

Reuse the actual closed source box[nested,outer], where nested is raw false Mu over nullary tag17 and outer is raw false Mu over union[var0,nested]. Derive the target outer full Mu, its original-build Written/Stored, then base Observed and apply the NEW consumer once. Do not supply a desired terminal or choose an opaque writer by equality.

There are two distinct proof obligations. First classify any recovered original Reached binder expression in that finite source. The candidates are nestedBody and outerBody. The actual closed nullary-node callback shape cannot equal the selected outer stored body, which is a full inner Mu; this excludes nestedBody without a unique writer or exact-event equality. Prove this shape fact from the actual Context/callback, rather than assume it.

Second, once event.expression=union[var0,nested], invert the newly returned pure UnionDescent and the retained nonunion node-or-binder kind. The only terminal syntax choices are var0 or nested. The kind excludes var0, so that SAME returned terminal must be the nested binder. The actual SourceRow and resumption tuple under those witnesses then demonstrate the binder arm. Duplicate occurrences, event.before equality and a unique historical creator are unnecessary.

Both obligations are unproved fixture work. The present fixture3c951a0c only demonstrates actual warm member1 binder resumption directly; the current observed consumer correctly exposes a disjunction. Do not describe it as a forced binder example. The prior initial-capture family can separately exercise ordinary node rows and changed Calls. Keep source-family and fixture-version counts separate.

## Scope boundary

Written and Stored remain independent existential propositions unless a later API explicitly shares their hidden event. The enclosing writer and a resumed historical winner may differ. This addition proves source-union descent for a chosen correlated terminal; it does not prove original lexical occurrence uniqueness, a strict requester-to-winner syntax inequality, general generated-capture ancestry, completeness of residual Mu observations, a global renewal rank or termination. No native execution or Haskell refinement claim is added.
