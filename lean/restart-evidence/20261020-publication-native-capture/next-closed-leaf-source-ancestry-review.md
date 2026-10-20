# Closed stored-leaf source ancestry review

Reviewed on 2026-10-20, Europe/Stockholm. This is a read-only source audit. No Lean, Haskell, or package checks were run. The proposed theorem below is not proved by this review.

The next useful producer is an indexed open-ordinary leaf handoff. It must connect an actual completed source node build to its selected canonical row, the original source RowCall, and the actual source child build. This is smaller than a general leaf ancestry relation. It gives source induction a genuine child call without assuming its desired ancestry conclusion.

## Existing boundaries

`InternedStoredSubstitution.leaves` stops at every closed value before inspecting its constructor. Thus `leaves closedValue = [closedValue]`, including a closed ordinary node, union, or Mu. An indexed closed leaf can equal the entire input value. No unconditional strict physical-value decrease follows from being a leaf. For an open node, leaves are the ordered concatenation of leaves of its row children. Open union members and open Mu bodies are traversed in the same way.

`InternedStoredSubstitution.leaves_available` proves availability of each listed leaf. `InternedStoredLeafShape.leaves_shape` proves that a leaf is closed or a reference. `InternedStoredLeavesOrdinary.leaves_ordinary`, `manyLeaves_ordinary`, and `edgeLeaves_ordinary` track an uninterned free name by list membership. None retains an indexed closed-leaf occurrence or a source syntax call. Their free-name premise does not apply to a closed leaf.

`SourceCurrentBuildStructuralRowOrigins.build_row_origin` already produces the exact ordinary `SourceRow.node` receipt from a selected structural row. Its RowCall retains original source row index, complete symbol and guard, actual ordered child build, source prefix and suffix, Context at the child-list entry, and growth into the completed source heap. It also retains canonical output row index separately. Its union case retains the actual source-member call. Its binder case stops at the selected stored body, including a warm winner.

`SourceCurrentStoredMuRetainedAlignment.RowCall.called` is the needed actual Fresh `buildMany children inputs current = .done values middle`. Its `children_eq` connects the row's physical children to these actual outputs. The Fresh indexed child extractor exists as PRIVATE `SourceCurrentBuildStructuralRowOrigins.member_call` at lines 188-226. It derives the indexed child syntax, exact prefix and suffix, actual child build, and Context at that call.

The public `SourceCurrentSubstitutionRowExecution.ChildTrace.children` and `.indexed` instead extract calls of `build (encode context locals original)` from encoded stored reconstruction. They are useful for that separate interval. They do not identify the earlier Fresh source syntax that first produced an original child. `rows_indexed` and `node_indexed` in the same module preserve this distinction.

`SourceCurrentStoredLiteralRowLineage.RowAt` descends through union members and Mu bodies. Its ordinary case selects a root row. It does not descend through ordinary children. Therefore a row inside a closed child leaf is not automatically RowAt of the enclosing node. `ClassRecursiveValueOrigins.Occurs` is only an ordinary-child occurrence relation for its constrained value model; it does not implement the encoder's union/Mu/closed-stop traversal.

## Proposed precise producer

A useful sole public endpoint is `node_leaf`, with this contract, using the current Context and Fresh build types:

```text
Context before inputs
build (.node expressions) inputs before = .done raw after
raw.free != []
(leaves raw)[leafIndex]? = some leaf
------------------------------------------------------
exists outputIndex row childIndex child inner sourceIndex
       symbol guard children rows middle call childSyntax current next,
  (nodeEdges raw)[outputIndex]? = some row
  row.children[childIndex]? = some child
  (leaves child)[inner]? = some leaf
  leafIndex =
    (edgeLeaves ((nodeEdges raw).take outputIndex)).length +
    (manyLeaves (row.children.take childIndex)).length + inner
  call : RowCall expressions inputs before rows middle after
                   sourceIndex symbol guard children
  call.output = row
  buildEdges expressions inputs before = .done rows middle
  run (makeNode rows) middle = (raw, after)
  children[childIndex]? = some childSyntax
  call.values[childIndex]? = some child
  buildMany (children.take childIndex) inputs call.current =
    .done (call.values.take childIndex) current
  Context current inputs
  build childSyntax inputs current = .done child next
  buildMany (children.drop (childIndex+1)) inputs next =
    .done (call.values.drop (childIndex+1)) call.middle
  sizeOf childSyntax < sizeOf (.node expressions)
```

The indexed leaf assumption need not additionally assume leaf closed; this stronger handoff works for reference leaves as well. The caller can retain its actual `leaf.free = []` fact. The output is a real strict source-child call, not a strict generated-child bound.

The proof needs one pure indexed append decomposition of `edgeLeaves` and `manyLeaves`. Then `build_row_origin` selects the actual RowCall. Its `children_eq` supplies the indexed child output. The existing private `member_call` proof supplies the Fresh child interval. A new endpoint can copy that small extraction or expose it in its own module without changing the frozen source. Availability and growth can be derived from the actual Context/callback facts if a consumer needs them. No future call or reader-wide lexical availability is required for this extraction.

The closed-root case must remain separate: derive `leaf = raw` and `leafIndex = 0`. If a selected row inside that closed leaf is available, apply the existing `build_row_origin` directly to the same completed build. This can yield the ordinary row call even though the encoder captured the whole node. It does not justify another strict value step. An unconditional node-leaf endpoint should expose exactly this alternative rather than exclude closed results silently.

## Composition with publication and native slots

For a selected stored body, first obtain the actual earlier source build from its selected writer. `SourceCurrentCompletedBuildRootedWriters.build_writer_or_prior` supplies either the exact prior complete cell or a same-publication rooted Written witness. The planned fixed-publication raw-source producer must supply the historical callback/body build. The leaf handoff can then follow actual ordinary child calls of that historical expression. At an open Mu boundary it must recover that Mu's selected writer again; the current callback is not interchangeable with the winning stored body.

For a source variable, `SourceCurrentSourceCaptureOriginalSlots.original_slot` maps a ROW-BEARING capture along an actual source Path to its original input suffix index. It requires that Path and RowAt of the captured value. It does not prove an origin for every closed capture, such as Empty, and it does not relate a native encoded build's nonempty initial leaf list to an earlier compiler input. `empty_initial` cannot eliminate captures in a later native build whose initial inputs are `leaves body`.

Keep three positions distinct: source row index, canonical row index, and leaf-list occurrence index. In addition, `encode` uses `slot`, which is `findIdx` by `referenceOf`, not the chosen leaf occurrence index. Repeated equal leaves can occur at multiple positions; encoding chooses the first matching identity. For example, two repeated closed child leaves give two leaf occurrences but their encoded variables can use the same first slot. An indexed origin theorem must retain the actual occurrence witness or explicitly prove the slot-to-occurrence equality it uses. It must not assert unique occurrence or source/output index equality.

## Recommendation and remaining obligation

Implement the single indexed source node/child handoff before a general leaf ancestry hierarchy. Combine it with the already assigned native leaf/self classifier and rooted publication raw-source producer. The remaining general proof must handle closed-root stopping, exact capture suffix origins, normalized union source membership, and the selected historical binder winner as separate cases. Actual nested Mu source syntax can remain unrestricted. This audit establishes no general source ancestry, binding renewal, whole-library completion, or runtime defect.

## Exact reviewed source bytes

- `lean/MicroCFTA/InternedStoredSubstitution.lean`: SHA256 `b81ad8ef37080a927fbb6664f6c2ff89da0fbefe5fc775bc55af9b1b8049b9e0` (12151 bytes).
- `lean/MicroCFTA/InternedStoredLeafShape.lean`: SHA256 `088584f99af2100dbab7c973914eabbfcd360727de3b0f76a39cb2a050b7b8cc` (2446 bytes).
- `lean/MicroCFTA/InternedStoredLeavesOrdinary.lean`: SHA256 `1f53a1c87c39142d68fab94ab0ad5e1e7fd6e8bc1dc2bb734cc30ef55de8f94c` (4850 bytes).
- `lean/MicroCFTA/SourceCurrentBuildStructuralRowOrigins.lean`: SHA256 `e2d956d21a707f5ec052f1c929286ca8742353d884b90fabfe7e8a07831c89b6` (19701 bytes).
- `lean/MicroCFTA/SourceCurrentStoredMuRetainedAlignment.lean`: SHA256 `5de96cd99e0a0cfac56651bfd8cf50879f51a9c9de85bbbc900866694447793b` (19434 bytes).
- `lean/MicroCFTA/SourceCurrentSubstitutionRowExecution.lean`: SHA256 `de4f42e7d1f2b423a473c3960f5702277818806c605cf5130dffcdefcd58d2cb` (15191 bytes).
- `lean/MicroCFTA/SourceCurrentStoredLiteralRowLineage.lean`: SHA256 `d04385883eb67f7c365d8c4a7492429ba8dcbe677b7a6a6be7e73d2ed54ddd1b` (19383 bytes).
- `lean/MicroCFTA/SourceCurrentSourceCaptureOriginalSlots.lean`: SHA256 `e731cbde505316518b862eb57688d92d167ce51307cb36d2639d241bbe3453ad` (3412 bytes).
- `lean/MicroCFTA/SourceCurrentCompletedBuildRootedWriters.lean`: SHA256 `cfba7a49a41189cc354676d1091bdfe44eb74072c3f859190f43b3545a1a1e18` (24038 bytes).
