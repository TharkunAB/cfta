# Next actual Mu row alignment

Source-only design review, 2026-10-20 21:09 CEST. No Lean jobs or repository edits. The proposed adapters below are not checked theorems. The attached source-pins JSON records the exact reviewed bytes.

## The smallest meaningful immediate step

SourceCurrentPublicationBodySourceRows.written_body_origin (71–103) already consumes the SAME CompletedBuildRootedWriters.Written returned by CapturedMuRowProduction.capture (60–61). It returns the selected publication event, full Mu payload equalities, original generated-root Reached, actual raw reserved-body build, exact filter, rich Context, raw RowAt and SourceRow. It has no Ready or future replay premise. Its fixed-event foundation publication_body_origin (26–68) preserves the original root and source callback entry. This is stronger actual callback provenance than an Empty/profile observation.

A shared StoredRows receipt is therefore a substantive additive composition. Unpack the rooted Written once, align entry/body/depth/ordinary by Mu injectivity, and obtain the raw callback, Context and Reached once. Store the actual build and filter before the universal clause. Then derive

    forall row, RowAt body row -> RowAt raw row ∧
      SourceRow event.expression
        (reference (interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter row

for that SAME event/raw/rawAfter. This uses callback contexts and actual callback_raw, the normal/raw-available filter_row equivalence, then build_row_origin. It does not need a new source ancestry premise. It must not independently call an existential writer selector for every row. The fixed event's generated source root is the encoded parent program. It is not automatically the original user program.

Capture can call CapturedMuRowProduction.capture once and append this StoredRows receipt inside its existing generated tuple, consuming that tuple's exact rooted Written. The initial full-cell arm remains the exact initial cell. The strict earlier prefix bound, exact used pair, Context/build, full payload and generated row producer remain unchanged. A stored structural row can be nullary or occur below a retained Mu: RowAt intentionally has an opaque body constructor. This is actual physical source provenance, not an assertion that such a row has already been observed by unfolding.

## Actual unfolded rows need an additional, different alignment

An observed literal row after unfolding can have rebuilt children. It must not be assumed to equal a stored body row. The strongest applicable existing producer is StoredLiteralRowLineage.execute_row (201–256), followed by source_row (137–145), not nodeEdges of the Mu and not profile readback.

Let mu := Value.mu entry body depth ordinary and env := fun name => if name = interned entry.identity then some mu else none. For an ACTUAL successful repaired unfold at a supported heap h,

    unfold mu h = done value after
    Row value row

unfold is definitionally execute body env (InternedFreshOrdinaryStoredSubstitution, 75–85). execute_row applied to source=body derives Origin env body row, including original union/member and nested stored-Mu cases. Every possible env replacement is the full Mu itself, and LiteralRootParts.Row has no Mu constructor (25–32). Thus source_row's replacement exclusion is DERIVED, not assumed. Its result is

    exists original, RowAt body original ∧
      row.symbol = original.symbol ∧
      row.guard = original.guard ∧
      row.children.length = original.children.length ∧
      (row = original ∨ exists lexical current next,
         Calls lexical original.children current row.children next).

This works for nullary rows. It retains complete row fields and actual ordered child calls. It does not retain the output canonical row index in the RowAt proof, although the caller may retain that lookup separately. It does not identify an output child with an unchanged source child. StoredMuUnfoldChildContexts.unfold_child (289–321) already strengthens the nonnullary case with the selected child index, exact source child, its structural size bound, actual lexical execution and physical/issued intervals. It requires a child, so it cannot serve as the sole nullary-row consumer.

The resulting original stored row is precisely the row argument for SAME-event StoredRows. Compose against the same captured Mu payload, not against a newly selected current callback. This maps the unfolded row's full fields and actual child Calls to a real source-row occurrence in the historical reserved callback. It does not equate those child values across reconstruction.

## Derive physical publication history at the right endpoint

Native memo History does not supply NativeMuPublication.History. CapturedMuRowProduction.capture currently has the former and an initial SemanticHeap; it does not carry the latter. A sufficient natural added initial premise is physical History empty before.heap, derived by closed_history for actual empty source construction. NativePublicationTrace.from_history (147–152), using the SAME actual query prefix and initial SemanticHeap, derives physical History empty current.heap even while its native owner is evaluating. No History is inferred backwards from growth or from a returned memo-cell map.

For the actual unfold above, derive Available h mu from the indexed leaves lookup and parent availability. Its body is available as a child; env replacements are available because they are the same full Mu. StoredLiteralCalls.execute (20–40) derives semantic/physical/issued effects from the actual body call. Form the exact encoded body-build Context from those initial semantic facts and inputs_available. NativeMuPublication.build_history (167–169) derives the actual publication interval h -> after from that exact encode build. Rewrite its stopping state with the supplied actual successful unfold and compose with the initial physical history. Use after as execute_row's reader, with Grows.refl. This removes the otherwise false requirement Grows after current.heap and needs no future enclosing completion.

Minimal local adapter proposal: actual unfold + initial SemanticHeap/Available full Mu + physical History empty h + selected literal Row -> the full stored-row anchor/fields/Calls above, with exact actual return and effects. It can be composed with capture/StoredRows without changing the captured writer. It need not synthesize any History at an arbitrary external graph view. If the caller only has Origin view [unfoldedValue] row through another retained Mu, the literal Row premise is not available; retain the residual actual Mu observation chain or classify its last actual unfold separately.

## Why the older alternatives do not close this gap

StoredMuRowOrigins.mu (68–75) only quantifies physical nodeEdges of execute(mu). StoredMuLiteralRows.mu (65–83) extends that to literal root-union rows and reconstructs a nested source Mu's original-body call. Neither is a direct outer unfold theorem: outer unfold executes body, not execute(mu). Their causal history premise is physical History at a suitable later reader. It can be produced by the actual interval above, not by native memo History.

NativePublicationNodeAlignment.publication_node (52–73) proves full finite-observation Related for node-root publication expressions with strict child Aligned premises. The BinderFree corollary (196–226) derives those premises for that static fragment. The module explicitly excludes arbitrary union/binder roots and older-winner comparison. An arbitrary generated encoded parent can have those roots or nested binders. The theorem cannot be applied without deriving its shape and child premises from actual syntax.

CausalStoredMuReadback.complete (34–75) derives actual sequential body/ordinary calls, profile equivalence and physical Empty agreement from Ready and causal physical history. Profiles do not identify rows or reconstruct child lineage. It also constructs later readbacks, not the caller's already selected exact observation. It is not an all-depth alignment substitute.

Publication.winner (257–273) preserves keep-first: a candidate's finish can select an older completed payload. History.from_empty (330–336) recovers a writer for a selected resident full Mu, but using it independently could lose the rooted event already supplied by capture. Use capture's SAME rooted Written for source ancestry; use physical history only for causal row/readback facts. Original-source rooting of the initial-cell arm, stored-winner/current-callback equivalence, arbitrary residual Mu observations and a global renewal bound remain open.

## Exact dependency hashes

- `lean/MicroCFTA/SourceCurrentPublicationBodySourceRows.lean`: `f226968e7084fb2d6161760c2e41b850d2ebd984c6bf4c94281cf98be45203de` (6826 bytes).
- `lean/MicroCFTA/SourceCurrentNativeCapturedMuRowProduction.lean`: `5e341ad85646100c59f45ca1f27824c23f1437ce89b09cbca2fba9a1e804c591` (5721 bytes).
- `lean/MicroCFTA/SourceCurrentNativeMuPublication.lean`: `e24184ee19ac4028a3e1604a82fc3cfea92f4b40d5a8490d08f02143b049efb2` (24007 bytes).
- `lean/MicroCFTA/SourceCurrentNativeMuPublicationCallbacks.lean`: `fcf760e62065456344180f8edcc4495a784006c73d087d06d47ab0f2a26b0395` (6552 bytes).
- `lean/MicroCFTA/SourceCurrentNativePublicationTrace.lean`: `4ff343a0f36566dafca6ecd3c96e3c8c82f9d11c0027676b1283dd1885b38218` (12889 bytes).
- `lean/MicroCFTA/SourceCurrentStoredLiteralRowLineage.lean`: `d04385883eb67f7c365d8c4a7492429ba8dcbe677b7a6a6be7e73d2ed54ddd1b` (19383 bytes).
- `lean/MicroCFTA/SourceCurrentStoredLiteralCalls.lean`: `b5f049a31c89dee1fb1f4d2fa9c37523eddc3bc022c9ff0f7cc7407083a03ba8` (10771 bytes).
- `lean/MicroCFTA/SourceCurrentStoredMuUnfoldChildContexts.lean`: `24b36c50bbcf0249d0c7cbf1059607b7e9814e198b011564af211428171bf1cb` (23043 bytes).
- `lean/MicroCFTA/SourceCurrentStoredMuLiteralRows.lean`: `df95c7290772562d8f0656ddd0ab6364116148a0357a57307bcddba811535c9e` (10351 bytes).
- `lean/MicroCFTA/SourceCurrentStoredMuRowOrigins.lean`: `abbca6b32e0045a995c627c3e5d007e98b06021962ecb3aef6c0fdb7c6a5d200` (10981 bytes).
- `lean/MicroCFTA/SourceCurrentNativePublicationNodeAlignment.lean`: `708b81d7b2517064e22c4bf8c1565c8cb1b4502a04f85a97fd5a32c63299d4ac` (14122 bytes).
- `lean/MicroCFTA/SourceCurrentCausalStoredMuReadback.lean`: `48129c782ea4c630b0f15e1ebecd1938d7ecb74afcd433dce7e3a1d49fdac5a0` (5046 bytes).
- `lean/MicroCFTA/SourceCurrentLiteralRootParts.lean`: `d2d0bddaf1aa4f3397505ca751915b04ebf190a528c8c27db53255c29cbea4df` (2906 bytes).
- `lean/MicroCFTA/SourceCurrentNativeOriginExposure.lean`: `20ecd0f0f4ae76264f1cc59f44aee95181c095de0e65f5dc4ee8ff749b8bf046` (11092 bytes).
- `lean/MicroCFTA/InternedFreshOrdinaryStoredSubstitution.lean`: `526f58eb47bd9475634b88190adab66eba0912e23a7c4fc1d122eb4bd10be66f` (6530 bytes).
