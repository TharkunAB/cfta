Stage 2 generalizes only eager_captured_resources. The final carrier is SourcePruningEnumerationSharedEagerReservation-stage2-UNCOMPILED.lean. Status: UNCOMPILED.

The exact input is the immutable stage1-v2 carrier at SHA256 bc895cbf6221c077b9b0dea6e32c769c688b7b2555314643bbd7272780516754. Root reported that carrier passed strict private check2 at 11:56:57. Live source still had the older 293175ca identity at acquisition, so this task used the approved immutable carrier and did not rely on promotion timing.

Final SHA256: 1f537303110606e498d6a9cd1f7e1f87287f9485b0af87bd1bcc648f9f57e11a. The file grows from 8,333 to 8,395 lines. Net change: 62 lines. Apply stage2.patch to the exact bc895 baseline.

The new private eager_captured_resources_with_narrow takes the actual narrowing operation. Its induction input is EagerResumeWithNarrowComplete for that same operation. Its hook uses resumeWithNarrow and the unchanged eagerChild. Its completed-fragment branch calls the checked callback_eager_induction_resources_with_narrow. All other captured child preparation, tuple consumers, finalization, actual caller/query endpoints, captured heap, bounds, and reservation operations retain the original proof text.

The old eager_captured_resources retains its exact complete header. It specializes the generic theorem to SourcePruningOuterNarrow.narrow holeKey keyMatches admits. The specialization explicitly supplies (bits := bits). All source bytes outside ActualCapturedResources are identical, including the checked stage1 declarations, child/tuple/row kernels, captured-row helper, opaque/prepared/expansion helpers, whole-depth closure, public laws, and imports. The operational worker is unchanged.

The generic theorem has no Key/fits/admits parameter. The existing numeric Fits input remains unchanged. The induction hypothesis is an internal property of the actual smaller-depth worker. It is not a new final source or worker premise. This stage does not prove the whole identity induction or all-fuel safety.

Forward and inverse unified-patch replay pass. The exact old header comparison passes. The baseline and candidate carriers, old header, complete generic declaration, patch, source lineage, and portable metadata verifier are retained. No compiler, evaluator, runtime probe, Git, board, live-source, or Haskell operation ran here. No Haskell fix or defect was found. No FINDINGS change is needed.

Use the existing Root serial strict-check controller. The module target is MicroCFTA.SourcePruningEnumerationSharedEagerReservation. There are no new imports. COMPILE-NEEDS records the correct namespace for optional private axiom reports and the later Audit target.

Full carriers are retained for the requested replay. Semantic review covered only the named captured declaration and its section boundary, plus relevant already-owned callback contracts. Carrier retention does not claim full semantic review of all 8,395 lines or reset any historical original-source union, whole-slot history, permanent failure, or UNKNOWN.
