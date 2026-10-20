# First-cut composition with actual source child calls

Read-only design review on 2026-10-20. No Lean runs or repository edits. New signatures below are proposals, not checked declarations.

## Smallest genuine missing producer

Expose an actual indexed Fresh RowCall child extractor without an open-result premise. The relevant generic Fresh member_call is private in BOTH SourceCurrentBuildStructuralRowOrigins and SourceCurrentOpenOrdinaryLeafSourceCalls. The inspected public SourceCurrentSubstitutionRowExecution.ChildTrace.indexed extracts encoded stored reconstruction calls; it is not the earlier arbitrary source Syntax buildMany. SourceCurrentSourceChildDepth.node/union provides actual constructor decompositions and depth inequalities, but no indexed child prefix/build/suffix. No public general Fresh RowCall.indexed_child with the required rich Context and exact slices was found in the source search.

Prefer one public RowCall.indexed_child producer rather than another leaf flattener. Keep the reusable actual Fresh member_call inversion private in the new module unless another public caller genuinely needs it. Suggested essential contract, with all indices explicit:

```lean
row_child
  (context : Context before inputs)
  (call : RowCall expressions inputs before rows rowsAfter reader
    sourceIndex symbol guard children)
  (index : Nat) (child : Value Symbol Guard)
  (selected : call.output.children[index]? = some child) :
  ∃ childSyntax current next,
    children[index]? = some childSyntax ∧
    call.values[index]? = some child ∧
    buildMany (children.take index) inputs call.current =
      .done (call.values.take index) current ∧
    Context current inputs ∧
    build childSyntax inputs current = .done child next ∧
    buildMany (children.drop (index + 1)) inputs next =
      .done (call.values.drop (index + 1)) call.middle ∧
    Grows before current ∧
    Extends before.nodes.issued current.nodes.issued ∧
    sizeOf childSyntax < sizeOf (Syntax.node expressions)
```

This uses the SAME full source row and ordered child index. First derive the rich row-entry Context from context.edges on expressions.take sourceIndex and call.earlier. Rewrite the selected child with call.children_eq. Apply actual Fresh member_call to call.called and that exact index. Actual prefix effects derive Grows and issued extension from before to the selected child entry. The two original syntactic lookups, call.source and children[index], give strict source-Syntax size with the exact generic default Symbol/Guard SizeOf measure. No returned-value or self size is compared. RowCall.context alone is the older base Context; retain the supplied original rich Context to recover the joint depth component through the actual prefix.

This applies to CLOSED ordinary results as well as open ones. It never requires a leaf lookup in leaves(call's entire raw result). A closed raw result stops as one leaf, but its complete source row still retains ordered child calls. Normalized unions can merge a closed ordinary member with an open ordinary member into an open ordinary parent. The full selected parent row can then come from the closed source member. This is why node_leaf's opened raw premise cannot serve as the sole general consumer. The definition-level example union[node f[closedLeaf],node g[Depth]] illustrates that boundary; no new computed fixture is claimed here.

## General source consumer and the three stops

For the cut branch, use Cut.facts to retain RowAt raw parentRow, the SAME parentRow.children[childIndex] lookup and leaves(child)[inner]. Apply actual build_row_origin to parentRow, not to an alleged unchanged lexical leaf of an original union member.

A focused source_child_or_stop producer can take the resulting actual SourceRow, original Context before inputs, and optionally Reached originalRoot initial expression inputs before. It derives one of these three alternatives. Structural recursion follows ONLY the SourceRow.union constructors; no desired ancestry induction hypothesis is supplied publicly.

- Node: retain the exact SourceRow.node built/made receipt and its original RowCall with output = parentRow. Pass the SAME selected child index to row_child. Return the actual smaller source child call and rich Context, keeping leaves(child)[inner] unchanged. If recursive source unions precede this node, their true original member lookups and actual source call slices remain attached to the supplied SourceRow proof. The node-child strict bound also lifts through those genuine source-union syntax memberships to the supplied source expression.
- Capture: stop at the actual SourceRow.capture slot, its exact captured value and RowAt captured parentRow. Retain the SAME child/inner continuation below parentRow. With the derived Reached path, existing SourceCaptureOriginalSlots.original_slot identifies the exact initial suffix slot. Its row-bearing premise is the PARENT row in the captured value, not an invented RowAt for an ordinary descendant leaf. Empty original inputs exclude this arm only when that original rooted source Path is actually available.
- Binder: stop at SourceRow.binder's historical current call and actual depth/ordinary callbacks, request, selected Mu cell, actual smart finish and RowAt of parentRow in the SELECTED stored body. Keep all four selected Mu fields. Do not assert that the selected body came from the current requester callback. Rooted writer provenance requires the actual enclosing completed-build receipt and build_writer_or_prior; a pre-existing selected cell remains a prior-cell alternative until its own causal receipt is supplied.

A separate duplicated event hierarchy is unnecessary. The current SourceRow proof already retains the actual source-union prefix/call/suffix and nested proof. A consumer can recurse on that proof and return its terminal node/capture/binder receipt. If the public conclusion must expose the complete selected union route, add a small proof-indexed union-only descent witness tied to that SAME supplied SourceRow, rather than an arbitrary terminal SourceRow or unrelated Grows witness. Do not discard the actual source-union index chain and later replace it with an equal-valued member. The low-level row_child producer above is the useful first implementation even before a final public terminal-result format is chosen.

## Original source route at the exact child entry

Reached is needed only to preserve a larger pre-existing original root. A standalone source call can use reached_initial expression inputs before. It does not need an extra original-root Context if Context before inputs is already the actual support at this call. Earlier root construction support is used to derive that Context by actual execution, not assumed at each intermediate child.

At a SourceRow.union step, source supplies the ORIGINAL syntax member index. Reached.union extends the syntax route using that actual membership. The actual earlier buildMany call and original Context derive forward Grows before current. Reached.grows then places the route at the exact nested call entry. Its supplied Context current inputs is the rich Context for recursive consumption. The full parentRow and its child continuation do not change.

At the node step, call.source and the exact childSyntax lookup justify Reached.node. Derive Grows from before to call.current from call.earlier, then from call.current to current from the selected child prefix. Reached.grows through those two FORWARD intervals gives Reached originalRoot initial childSyntax inputs current. RowCall.current_growth points toward its later reader; it cannot be reversed to obtain either prefix. No physical Grows interval manufactures native memo History or a writer at another checked reader.

The stored Cut.union index is a position in the normalized raw value's members with a leaf-prefix offset. SourceRow.union's index is a position in ORIGINAL source expressions and their actual buildMany outputs. Flattening, ordinary merging and deduplication can change that relationship. Retain these two routes separately. Full parent-row identity, then SAME ordered child lookup, is the compositional link. There is no assumed equality of those union indices, no same-leaf-membership transport, and no leaf-occurrence/encoder-slot identification.

## Boundary of the result

The proposed producer gives a true source child execution or an explicit capture/binder stop. It does not close those stops by assuming past-writer ancestry. A closed whole root may stop directly with RowAt raw row. A native encoded root can begin with nonempty captured whole values. An earlier winner can have different source syntax from its current requester. The whole-Mu self replacement has no strict self decrease. No global renewal, owner exclusion, termination, observation Origin, or Haskell correspondence follows from this local composition alone.

Exact ROOT-relative foundation pins and the separate HERE candidate pin accompany this note. The Cut candidate is 98e3f0059871cf60a9fa68b976c1975a7cf4a791e612d351740de020d7aa1deb. Its facts/split were read; this audit adds no check or promotion claim.
