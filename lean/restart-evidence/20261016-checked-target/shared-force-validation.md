# Checked shared target Force validation

Source: `lean/MicroCFTA/SourceCurrentAllocatedSharedTargetForce.lean`.
Frozen SHA256: `041e17546ab5e935be5d9aac1f9ea0ccc0c3e7e46385cf29bd67e107879585e1`.
Source length: 192 lines. The frozen copy has identical bytes.

The pinned Lean 4.34.1 canonical build passed with terminal status 0 and 1282 jobs. `shared-force-build-4.log` records the result. Its only warning is the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`. The first three logs preserve local elaboration errors in the new Reads constructors. Explicit constructor index types and record/value indices resolved those errors. The canonical slot was released before direct probes ran. No old proof file was edited.

Direct Lean validation passed on its first attempt with terminal status 0. It checked all six public theorem axiom reports and eleven public signatures, including the five graph, receipt, and range definitions. Three integration kernels each have an axiom report and full signature. The log therefore has nine axiom reports and fourteen signature checks. Three bookkeeping theorems are axiom-free. The remaining reports use only `propext`, `Classical.choice`, and `Quot.sound`. The log has no error, warning, or `sorryAx`.

The raw Force graph has no semantic or inventory parameters. Its hit returns the identical shared State. Its miss takes only absence and the actual new TargetGraph.Target, then stores that exact result, checked state, and merge memo. Reads has a literal silent hit and a miss with the same actual TargetReads. ForceRanges requires TargetRanges only if the slot is absent.

`complete` derives the actual Force and its receipt from current shared Ready, captured Values at the base heap, selected class domains, coherent nontrivial record, path membership, reached ForceRanges, and initial global validity. `Force.verified` derives the receipt for an already supplied actual Force at its exact return. Neither endpoint assumes a future target receipt, successful callback, future Fields, model-validity law, or whole-forest closure.

The miss uses ClassTarget.finite or ClassTarget.actual_verified and Ready.store. The hit uses the historical SlotReceipt. The receipt derives the returned Ready at a computed inventory, actual physical Effects and Extension, closed available value, present slot, retention of every older slot, merge Extends, current global validity and unfolding retention, unchanged global query tables, and selected-subterm inclusion. The fourth memo is not called; Receipt.fourth_correct transports its earlier Correct property through actual Keeps.

Integration kernels:

- `required_cold_force` derives selected domains from an actual current Required receipt. It initializes empty target slots and derives the empty merge cache invariants. It constructs the actual force, present slot, and closed value without whole-forest closure.
- `force_then_hit` runs finite force, then constructs the literal hit at the identical returned shared State and exact same global bundle. Its current historical slot receipt derives availableclosed output and class-selected language without a second range plan or new inventory admission.
- `force_then_query` runs force, then the actual checked target/input query with only reached query WordRanges. It derives the next inventory, checked receipt, shared Ready after advancement, all prior slot retention, exact returned merge Memo, and the same stored target slot.

The completed serial graph does not establish callback allocation, noConstraint CAF demand or identity, HashMap iteration, GHC forcing, or pending publication. Leaf, structural class edits, the class pass, and the constrained outer caller remain separate proof components.
