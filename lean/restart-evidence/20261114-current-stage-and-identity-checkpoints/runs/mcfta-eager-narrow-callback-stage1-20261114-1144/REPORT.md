Stage 1 generalizes the actual eager recursion index and the first Left callback proof. Final candidate: SourcePruningEnumerationSharedEagerReservation-stage1-v2-UNCOMPILED.lean. Status: UNCOMPILED.

Baseline SHA256: 293175ca2f3b8b9f338c57e1b97eedac6c76a024155e5b30a4b8dc0cc3bddd30.
Final SHA256: bc895cbf6221c077b9b0dea6e32c769c688b7b2555314643bbd7272780516754.
The carrier grows from 8,282 to 8,333 lines. Net change: 51 lines. Apply stage1-v2.patch, not the retained first draft patch.

The new private EagerResumeWithNarrowComplete indexes the completion property by the actual narrowing argument of resumeWithNarrow. It retains every original Packet, Fits, Heap, selection, suspended-mass, reservation, stable-bound, OutcomeResources, and eagerFinal clause. It defines a Prop over the existing worker. It defines no new worker or evaluator.

The new private callback_eager_induction_resources_with_narrow contains the callback proof once. It executes the original recordTypes operation, uses its actual returned metadata and frame, and invokes the smaller-depth completion hypothesis at those actual inputs. Its work-fuel family installs the same eagerChild and fixed narrow argument at every continuation. It retains the exact final caller and queries. The proof body otherwise follows the original callback proof.

The old private EagerResumeComplete keeps its exact header and specializes the new index to SourcePruningOuterNarrow.narrow holeKey fits admits. The old callback_eager_induction_resources keeps its exact complete header and becomes a direct specialization of the generic callback theorem. The explicit original header files and replay checks are retained. The old zero theorem is byte-identical. Every source byte before and after ActualEagerCallback is identical. The child, tuple, row, reservation, prepared, expansion, and whole-depth proofs therefore retain their original text. No operational worker or Haskell file changed.

The generic declarations precede the Key section variable. They have no Key/fits/admits parameter. The configured specialization explicitly passes (bits := bits), because the result Prop does not infer that width. The first draft without this explicit argument remains intact. The v1-to-v2 patch records that source-review correction. Neither draft was compiled here.

There are no new imports. Existing callback/resource and backend imports already supply the required definitions. The metadata replay utility and exact header comparisons pass for the final baseline-to-candidate patch and its inverse.

The new induction contract is an internal target. It is not a final theorem premise and does not establish identity completion. The later induction must prove it for literal identity using the separately checked actual identity prefix capability. This stage adds no callback/provider premise to any old public theorem. It does not prove all-fuel safety, whole identity output resources, common assignment existence, or Haskell correspondence.

Compile the full staged carrier with the existing serial Root strict-check controller and its memory/swap limits. Rebuild the module and Audit after applying the exact pinned patch. COMPILE-NEEDS lists the module targets. No compiler, evaluator, runtime probe, Git, board, live-source, or Haskell operation ran in this task.

One metadata Python check initially searched for the first := token and matched the named argument (bits := bits). It stopped before writing source payloads. SOURCE-GENERATION-INCIDENT retains this event. The corrected check matches the exact saved header plus its declaration-specific proof delimiter. This was not a Lean failure.

The full baseline and staged carriers are retained for exact replay as explicitly requested. Only the named callback section, ambient notation, and declaration locators received semantic review in this task. Carrier retention and identity hashes do not assert a whole-module semantic review or reset any historical original-source union, whole-slot history, permanent failure, or UNKNOWN.

No Haskell edit, defect, or fix was found. No FINDINGS change is needed for this proof refactor.
