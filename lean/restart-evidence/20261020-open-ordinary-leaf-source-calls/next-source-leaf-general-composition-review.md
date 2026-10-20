# General source-leaf composition after node_leaf

Read-only review on 2026-10-20, Europe/Stockholm. No Lean, Haskell, or package jobs were run. No repository files were changed. The endpoints below are proposals, not established theorems. The reviewed node_leaf candidate has SHA256 `0ac93ff3acd3ca48e7e16657613bbe84fa6e1508cd6cb0be72eb10cffc8af2e4`.

## Smallest useful next result

Prove a general FIRST ordinary-child cut of the actual indexed leaf traversal. Then classify its exact parent row with the existing completed-source row producer. This avoids the false requirement that union normalization preserve the same leaf in an original member's leaves list.

The pure input is `(leaves raw)[leafIndex]? = some leaf` and `RowAt leaf row`. The output must be either `RowAt raw row`, or an indexed first-child receipt containing an exact parent row, child position, complete child value and remaining leaf index. The receipt traverses only union members and Mu bodies before that ordinary-child crossing. It retains the original leaf occurrence with exact list offsets. It derives `RowAt raw parentRow`, `parentRow.children[childIndex]? = some child`, and `(leaves child)[inner]? = some leaf`.

The execution-linked endpoint then has this contract:

```text
Context before inputs
build expression inputs before = .done raw after
(leaves raw)[leafIndex]? = some leaf
RowAt leaf row
------------------------------------------------------
SourceRow expression inputs before raw after row
OR
exists parentRow childIndex child inner,
  FirstChild raw leafIndex leaf parentRow childIndex child inner
  AND SourceRow expression inputs before raw after parentRow
```

`FirstChild` is a proposed small literal traversal receipt, not a desired source-ancestry relation. Its constructors should be:

- `node`: the value is open; an exact canonical row lookup and exact child lookup hold; the remaining child leaf lookup holds; the original leaf index equals the preceding rows' leaf count plus the preceding children' leaf count plus the remaining index.
- `union`: the value is open; select an exact member index; add the leaves count of the preceding members; retain the nested first-child receipt.
- `mu`: the value is open; retain the same leaf index and the nested receipt in the exact stored body.

There is no arbitrary endpoint constructor. The constructors derive the actual original lookup, full parent row and child continuation. No observation/epsilon Origin, global Directed relation or future source law is assumed. The ordinary root constructor can use the pure indexed flattening argument already present privately in node_leaf. The union and Mu constructors concern the actual returned value, before any source-syntax reasoning.

`build_leaf_row_origin` can apply `build_row_origin` to the pure split's exact row or parent row. It needs no source-ancestry induction hypothesis as a public premise. This is a general source/leaf-to-row handoff. It does not yet give complete original binding ancestry. A later source child induction can consume its real SourceRow.node branch and the actual child call.

## Why a simple union_leaf is false

The encoder tests closedness before inspecting a constructor. A closed union has `leaves closedUnion = [closedUnion]`. Union construction instead calls `unionMembers`, flattens original union values, removes duplicate identities, and may merge ordinary members with makeNode.

A source-grounded boundary candidate is:

```text
mu17 = binder false (node [row17 []])
mu19 = binder false (node [row19 []])
innerSource = union [mu17, mu19]
outerSource = union [innerSource, var 0]
inputs = [reference Depth]
```

The raw Mu flag preserves each closed Mu even though its own variable is unused. The inner closed union has two distinct whole-Mu members. Its leaves list stops at the whole inner union. The open normalized outer union flattens that inner union and has the individual whole Mu values as leaves. Those whole Mu leaves are absent from the leaves of BOTH original outer member outputs (the closed inner union and Depth). Thus the proposed existence of an original member with the SAME leaf in its leaves list is not a sound general normalization law.

This audit has not kernel-checked that concrete source instance. Arity is separately checking it under `/tmp/mcfta-union-closed-leaf-normalization/`. The correct contract issue follows the inspected definitions; a checked runtime or Haskell defect is not claimed. If the instance is built as a Depth callback, select its RAW build result. The subsequent self filter can drop bare Depth and change closedness again.

The first-child proposal avoids this problem. Complete ordinary rows and their child values survive the relevant union row handoff, even when a closed whole member's leaf list is repartitioned. In a no-child-crossing branch, a selected row already has RowAt through the flattened union/Mu prefix and existing SourceRow can classify it directly. For a child-crossing branch, classify its full parent row first and retain the exact child below that row. Never assert that the closed leaf itself remains a lexical leaf of an earlier source member.

## Existing execution extractors and precise limits

`SourceCurrentOpenOrdinaryLeafSourceCalls.node_leaf` already derives a canonical row/child, original RowCall, exact Fresh source child build, Context, source-list prefix and suffix, and a strict ORIGINAL child-syntax bound from an actual open `.node` source call. It preserves the global leaf flattening offset. It does not cover a source union whose normalized result is ordinary, a source variable containing an ordinary value, or a source binder returning a retained ordinary body. The first-cut plus SourceRow approach covers those source constructor boundaries without pretending that result constructor and source constructor coincide.

`SourceCurrentBuildStructuralRowOrigins.build_row_origin` gives actual source node/capture/union/binder alternatives from Context, actual completed build and RowAt of that result. Its union constructor retains an exact original index, source member call, Context and prefix/suffix. Its node constructor retains the complete original RowCall. It already handles union flattening, deduplication, ordinary merging and rows under opaque Mu bodies. It does not descend ordinary children.

The RowCall's `called` is the actual Fresh `buildMany children inputs call.current = .done call.values call.middle`. The node_leaf candidate's private member_call extracts a selected child syntax and exact child interval. Public `SourceCurrentSubstitutionRowExecution.ChildTrace.indexed` instead extracts an ENCODED stored reconstruction call. It cannot substitute for this earlier Fresh source call.

A SourceRow union branch can be followed by structural induction on that receipt to its actual node/capture/binder alternative. Full row identity supplies identical ordered children at every step. The same selected parent-row child and its remaining leaf index are retained. Original source row index need not equal canonical output row index. Duplicate rows and equal leaf values do not give unique occurrences.

`SourceCurrentGeneratedUnionPreparation.source_members` derives all historical member calls and warm replays, but requires a later Ready reader, growth and parent availability. Those are unnecessary additions for the proposed historical handoff. `SourceCurrentLiteralUnionParts.row` and `.literal` support the exact row/whole-Mu union bookkeeping already used by build_row_origin. They are not the false same-leaf-list law.

## Reached paths, captures and historical winners

A standalone caller can root Reached at its actual source expression and initial captures with reached_initial. To retain a pre-existing larger root, supply its actual Reached route. Reached.node and Reached.union extend the syntax route. Then Reached.grows moves it FORWARD through the actual completed source prefixes to the selected child entry. The growth is derived from the actual prefix calls and their Context facts; no reader-wide lexical availability or backward replay is needed. node_leaf's RowCall growth fields point to the completed heap, so they must not be reversed to obtain a child-entry route.

For a row-bearing parent captured by a source variable, SourceCaptureOriginalSlots.original_slot can now apply to that parent RowAt. The first-cut design deliberately extracts this parent row before descending its ordinary child. It avoids falsely using original_slot directly on a leaf below a captured ordinary child, for which RowAt of the whole captured value was not given. The actual source Path is still required to map the callback prefix to original input suffix. Nonempty initial captures remain explicit. A missing variable index returns Empty and cannot produce the supplied row-bearing leaf.

A source binder branch must retain the selected stored entry/body and exact current request/finish receipt. SourceRow.binder and NativeRequestProbes.request_probes do this. Context alone does not supply rooted historical source provenance for a prior resident winner. CompletedBuildRootedWriters.build_writer_or_prior gives an exact initial cell OR a rooted SAME-publication Written event for an actual completed enclosing construction. It does not erase the prior-cell alternative. Further ancestry of that prior cell requires its initial causal receipt, or the no-initial-Mu special case. Do not infer an original source root from arbitrary issued Path or assume the current callback produced a warm winner.

For a known rooted winner, PublicationBodySourceRows.written_body_origin exposes that same publication's actual historical raw source callback. Filtering preserves RowAt of an exact full parent row, including rows under Mu. This permits the first-child continuation below that row to survive. Filtering does not supply equality of before/after leaf lists or their indices. Recover the row first, then use its unchanged children. Do not substitute the ordinary probe or current requester's body for the winning body.

## Stops and progress statements

A closed returned root produces the leaf itself. With RowAt leaf row, `build_row_origin` applies directly to that same raw result. There is no required child or strict value decrease. An open Mu's pure leaves traversal follows its exact stored body; source-syntax traversal at that point still needs the selected writer handoff above. The whole self replacement is the complete selected Mu and supplies no strict self decrease.

The only immediately justified strict progress is the actual node or union SOURCE child syntax for the corresponding completed source call. An earlier retained writer can have different or larger source syntax than the current requester. Re-entering it is a chronological provenance transition, not a syntax decrease in the current source. No global rank is proposed here.

Keep source syntax execution, stored encode/execute and lexical leaf identity separate. `slot` is a first referenceOf match; a leaf occurrence index can differ from the encoded canonical slot. Keep exact lookups/offsets. The proposed general producer does not prove all-source renewal, owner exclusion, outer completion, convergence or concrete Haskell correspondence.

## Exact source pins

The following ROOT-relative source bytes were inspected. This note does not claim new validation of them.

```json
{
  "files": [
    {
      "path": "lean/MicroCFTA/InternedStoredSubstitution.lean",
      "sha256": "b81ad8ef37080a927fbb6664f6c2ff89da0fbefe5fc775bc55af9b1b8049b9e0",
      "bytes": 12151
    },
    {
      "path": "lean/MicroCFTA/InternedConstructorTemplates.lean",
      "sha256": "75aeb072ce0cfb7bc8bad40843184743281de8aeac1001c13ad941692d23e3f8",
      "bytes": 46073
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentBuildStructuralRowOrigins.lean",
      "sha256": "e2d956d21a707f5ec052f1c929286ca8742353d884b90fabfe7e8a07831c89b6",
      "bytes": 19701
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentPublicationBodySourceRows.lean",
      "sha256": "f226968e7084fb2d6161760c2e41b850d2ebd984c6bf4c94281cf98be45203de",
      "bytes": 6826
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentNativeSelfCaptureSlots.lean",
      "sha256": "d1f417f248866ad639798d2f3274006800a8da8f57ccb23e39d8bd7ccd42c281",
      "bytes": 3942
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentCompletedBuildRootedWriters.lean",
      "sha256": "cfba7a49a41189cc354676d1091bdfe44eb74072c3f859190f43b3545a1a1e18",
      "bytes": 24038
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentSourceCaptureOriginalSlots.lean",
      "sha256": "e731cbde505316518b862eb57688d92d167ce51307cb36d2639d241bbe3453ad",
      "bytes": 3412
    },
    {
      "path": "lean/MicroCFTA/InternedFreshOrdinarySourceHistory.lean",
      "sha256": "2a9858f8a41cce3022b1406f244b9d4d1990c0a0708469f6159a6b16f893b8a5",
      "bytes": 18275
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentStoredMuRetainedAlignment.lean",
      "sha256": "5de96cd99e0a0cfac56651bfd8cf50879f51a9c9de85bbbc900866694447793b",
      "bytes": 19434
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentSubstitutionRowExecution.lean",
      "sha256": "de4f42e7d1f2b423a473c3960f5702277818806c605cf5130dffcdefcd58d2cb",
      "bytes": 15191
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentLiteralUnionParts.lean",
      "sha256": "7284dfe74faa0eea227fce87867ef5377f525ee5726f1b4a19200487d5b6f7d3",
      "bytes": 10782
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentStoredCallbackChildContexts.lean",
      "sha256": "910ca8f1de718a78aa506a02f118c6ff5d73669f2625e35ccda2bbb88d470c34",
      "bytes": 10632
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentGeneratedUnionPreparation.lean",
      "sha256": "1b5a74f38cb29a5eeb75bd4e6193abc0f5b91ea5002fc5c347aa68ca2b27a33e",
      "bytes": 20121
    },
    {
      "path": "lean/MicroCFTA/SourceCurrentNativeRequestProbes.lean",
      "sha256": "530eca132a55b737181003a65e77ad7c508f84d7437d4df56e4766b7768d4d26",
      "bytes": 1674
    }
  ],
  "external_candidate": {
    "path": "/tmp/mcfta-open-ordinary-leaf-source-calls/SourceCurrentOpenOrdinaryLeafSourceCalls.lean",
    "sha256": "0ac93ff3acd3ca48e7e16657613bbe84fa6e1508cd6cb0be72eb10cffc8af2e4",
    "bytes": 10252
  }
}
```
