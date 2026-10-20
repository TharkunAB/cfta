# Next native capture ancestry interface

Read-only design review. Checked 2026-10-20 15:42 CEST. No Lean jobs or repository writes.

## Recommended next theorem

Add one fixed-publication producer first. Destructure `CompletedBuildRootedWriters.Written` ONCE and retain that event and its `Reached` witness. Do not call `NativeMuIssuedWriters.Written.raw_contexts`: its result existentially selects an event and does not return equality with the caller's selected event. Equal candidate payloads do not prove equal publication records or source expressions.

The following is an UNCHECKED interface proposal. All listed ingredients already have actual source proofs:

```lean
publication_body_origin
  (event : Publication)
  (reached : Reached root initial
    (.binder event.smart event.expression) event.environment event.before)
  (row : EdgeValue Symbol Guard) (inside : RowAt event.body row) :
  ∃ raw rawAfter,
    build event.expression
      (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated = .done raw rawAfter ∧
    run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter =
      (event.body,event.afterBody) ∧
    Context event.allocated
      (.reference (.interned event.entry.identity) :: event.environment) ∧
    Reached root initial event.expression
      (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated ∧
    SourceRow event.expression
      (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated raw rawAfter row
```

The event is an input, not a newly chosen output. The original completed build supplies it through rooted Written. The row is exactly the row already selected in the stored body, including an opaque nested Mu body. This theorem needs no Ready reader or later replay. It retains historical callback heaps and does not assert an execute call on raw at an old stored-child entry.

Proof path: `PublicationCallbacks.contexts event` gives the reserved outer lexical Context. Actual reservation gives Available of the own literal reference. Extend that Context locally. `callback_raw` on `event.bodyDone` gives the exact raw build/filter pair. Actual `build_verified` and Context.build give Normal and raw availability at rawAfter. `StoredCallbackChildContexts.filter_row` transports the SAME row from event.body to raw. `BuildStructuralRowOrigins.build_row_origin` gives SourceRow at the actual historical call. Build `Crossing` with `Entered.fresh event.depth event.ordinary event.afterDepth event.cut event.depthDone event.ordinaryDone event.missing`; `Reached.enter` gives the same event's original source route into the callback. No table-growth-to-publication inference is needed.

For a later Ready reader, derive a replay of this SAME fixed callback with `GeneratedHistoricalContext.replay` and the rooted witness's callback paths, final growth, and issued extension. This is a later corollary. It must retain event as input or return the rooted Reached witness in the same existential. The historical theorem is smaller and avoids duplicating the existing replay proof first.

## Exact original capture slot

`SourceCaptureOriginalSlots.original_slot` already proves the needed suffix theorem. Given the reached callback path, descend only through the actual SourceRow.union calls, using Reached.union and actual prefix build growth. At a SourceRow.capture leaf with `inputs[slot]? = some captured` and RowAt captured row, it yields

```lean
∃ originalSlot,
  slot = crossings.length + originalSlot ∧
  initial[originalSlot]? = some captured
```

Here crossings are the actual path to THAT capture, including the selected publication's fresh crossing. The returned captured value and row are unchanged. Callback prefixes contain literal references, which have no RowAt. Do not add a duplicate generic original_slot theorem. An enriched fixed-event SourceRow consumer can package this result alongside the existing node and nested-winner arms if the next caller needs one result type. It must stop at SourceRow.node or SourceRow.binder, rather than silently assert every row is a capture. Nested binder arms still select their own exact stored winner.

## Native encoded self unfolding: separate classification

Actual repaired unfolding is `build (encode (leaves body) [] body) ((leaves body).map (input selfEnvironment)) before`. The generated source root and its initial inputs differ from the original source root and original inputs. They are not empty even when the original construction started with `[]`.

A small useful second producer can invert an ACTUAL lexical lookup at the SAME slot:

```lean
-- Let mu := .mu entry body depth ordinary and rho := selfEnvironment ... .
((leaves body).map (input rho))[slot]? = some captured →
RowAt captured row →
  (∃ leaf, (leaves body)[slot]? = some leaf ∧
      leaf.free = [] ∧ captured = leaf ∧ RowAt leaf row) ∨
  ((leaves body)[slot]? = some (.reference (.interned entry.identity)) ∧
      captured = mu)
```

This proposal follows from getElem?_map, `InternedStoredLeafShape.leaves_shape`, the literal `input` definition, and exact selfEnvironment. Every other reference stays a literal reference and cannot have RowAt. Closed leaves remain exact whole values, including closed Mu records. The self arm returns the COMPLETE selected Mu and can carry structural body rows; it must remain explicit. The canonical plan variable index is justified by `StoredSubstitutionScope.slot_lookup` using Coherent and Available leaves at its actual source heap. `build_closed`, `build_external`, and `build_local` retain the exact slot behavior below local binder prefixes. Actual source slots and plan slots are different indices; do not equate them without those lookups.

## True remaining ancestry boundary

The closed native-leaf arm gives an exact leaf of the selected stored body, not an original lexical input by itself. A leaf can occur under an ordinary child, which RowAt does not traverse. To compose that leaf with the original callback, the next proof needs actual indexed child/encode occurrence ancestry through the raw source row calls, and exact root-filter preservation. The self arm is a recursive return to the SAME Mu, not a strict source descent. A nested SourceRow.binder can reuse an older winner whose syntax differs from the current requester. `build_writer_or_prior` correctly retains that prior-cell case; it cannot root an arbitrary pre-existing winner in the current encoded source call.

The smallest immediate deliverable is the fixed-event historical callback producer. The native slot classifier then identifies the exact remaining closed-leaf and self obligations. Neither result supplies a global renewal bound, excludes native captures, identifies a winner with the current callback, or proves a recursive decrease. A historical/native reader stays separate unless an actual retained interval is supplied.

## Stable sources read

- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentCompletedBuildRootedWriters.lean`: `cfba7a49a41189cc354676d1091bdfe44eb74072c3f859190f43b3545a1a1e18` (24038 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentNativeMuIssuedWriters.lean`: `76596c03925f0a27bd41ffb50572114363a452e58e1ce9ae07603f0b914e1697` (14426 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentNativeMuPublicationCallbacks.lean`: `fcf760e62065456344180f8edcc4495a784006c73d087d06d47ab0f2a26b0395` (6552 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentBuildStructuralRowOrigins.lean`: `e2d956d21a707f5ec052f1c929286ca8742353d884b90fabfe7e8a07831c89b6` (19701 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentSourceCaptureOriginalSlots.lean`: `e731cbde505316518b862eb57688d92d167ce51307cb36d2639d241bbe3453ad` (3412 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentStoredCallbackChildContexts.lean`: `910ca8f1de718a78aa506a02f118c6ff5d73669f2625e35ccda2bbb88d470c34` (10632 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedFreshOrdinarySourceHistory.lean`: `2a9858f8a41cce3022b1406f244b9d4d1990c0a0708469f6159a6b16f893b8a5` (18275 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedFreshOrdinaryActiveOrigins.lean`: `dad1217ca54f7938e1a59d8ad70a7fbacbb978d862c4f777c320b3a0e56b2f6e` (16358 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedStoredSubstitutionScope.lean`: `f63f40ee1801b70a6ab5eb450b58b41abebd4ec0244c6cb20c28eaed2f6f8e35` (10781 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedStoredSubstitution.lean`: `b81ad8ef37080a927fbb6664f6c2ff89da0fbefe5fc775bc55af9b1b8049b9e0` (12151 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedStoredLeafShape.lean`: `088584f99af2100dbab7c973914eabbfcd360727de3b0f76a39cb2a050b7b8cc` (2446 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedFreshOrdinaryStoredSubstitution.lean`: `526f58eb47bd9475634b88190adab66eba0912e23a7c4fc1d122eb4bd10be66f` (6530 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentRecursiveHeadRowOrigins.lean`: `163ea355c8a595b9e53f194266c77dc30749acb48a71bed2c89fc1e6fb2f9c12` (14308 bytes).
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentGeneratedHistoricalContext.lean`: `00a5396245665d1b7a2a6f6c30be719e0291e13415eddbb3bd0c8e6f829a3f3d` (6083 bytes).
