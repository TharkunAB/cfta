# Initial-only Force and Leaf receipt route

Reviewed 2026-10-16 20:58 CEST. Read-only API review. No material defect found in `SharedProfiles.lean`, SHA `13c5745fa83ad5042db528e0fd40e780eceb6d0bb05fb80c16f8b09e3c580eb5`.

## Force construction

Use `SourceCurrentAllocatedFiniteOrdinaryTargetResources.target_complete` at line 196 directly on `operandPaths record.paths path`, the fixed captured `values`, `before.checked`, and `before.memo`. It constructs its own actual Target, stable worker return, TargetReads, full receipt, output profile, native stores, Merge profile store, Work trace, and supply bounds. It needs no old ForceRanges or TargetRanges input.

Current captured availability follows from `ready.captured.available` and `known : Values base values`. `ready.checked`, `ready.admitted`, `ready.stored`, and `ready.covered` supply the physical and semantic warm facts. The new profile store supplies `native`, `output`, and `merge` certificates. `SharedProfileBounds.record_target_bounds` derives the exact selected operand count bound and signed-path depth bound. `record_profile` widens the produced profile to the class-wide limit. The count is `record.paths.length - 1` for a coherent record and a selected member. It is not the whole class length.

On a miss, set `after = SharedTargetState.store before path value checked saved`. Assemble the public `SharedTargetForce.Receipt` fields directly:

1. `.actual = Force.miss absent targetActual` and `.reads = Reads.miss absent targetReads`.
2. `.ready = ready.store path member targetActual targetReads targetReceipt`. This public helper at `SharedTargetState.lean:138` retains every historical slot graph and its own historical inventory.
3. Effects, extension, availability, closedness, Merge extension, and global effect come from that same target receipt.
4. `.present` follows from the exact put. `.slots` preserves earlier cells because the selected slot was absent and other paths are unchanged.
5. `.included` follows from public `AllocatedClassTarget.receipt_included targetReceipt coherent active member`. It needs no language callback.

The existing `Force.miss_receipt` helper at line 95 is private. A new module cannot call it through its public name. Repeating its small public structure assembly avoids constructing a second Target.

On a hit, use `ready.receipts path value present`. `SlotReceipt.available` supplies current availability and closedness. `SlotReceipt.included coherent active` supplies selected-term inclusion. Effects, extension, slot retention, Merge retention, and the global effect are reflexive. The exact Work trace is empty. The complete shared state and current inventory remain identical. The new `stored.slots` field supplies the profile and height; the old semantic SlotReceipt does not supply them.

## Leaf construction and exact joins

Force first. At the exact returned shared state `middle`, call `SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources.finite` at line 79 with the returned target as LEFT operand and the current input as RIGHT operand. Use the force's computed inventory and its current global bundle. The target is available and closed from the ForceReceipt. Transport input availability with `forced.effects.keeps.available`; input syntax and its profile remain unchanged. Closedness can be derived from the initial coherent available finite-ordinary profile, or supplied as the existing narrow physical premise.

Widen the target and input profiles to common row and arity limits. Use a common height maximum. Initial headroom is the Force node or edge budget plus the native total Work budget at those common limits. The Force supply bound derives query headroom. Thus no LeafRanges, future capacity, or callback is needed.

Set the final shared state to `SharedTargetState.advance middle queryChecked`. This keeps `middle.targets` and `middle.memo`. Public `Ready.advance` at `SharedTargetState.lean:113` supplies current readiness and admission at the query's computed inventory. `SharedProfiles.advance_stored` retains slot and Merge profiles and accepts the actual new native and output stores.

Assemble the public `SharedTargetLeaf.Receipt` as in its private `of_parts` helper at line 86:

- `.actual = Leaf.apply forceReceipt.actual queryReceipt.actual`; `.reads` stores those exact receipts.
- Effects and extensions compose Force then query. Query availability and closedness supply the result facts.
- Slots and Merge extension use the Force facts because shared advance leaves both tables unchanged.
- The query global effect has identical incoming and outgoing bundles. Compose it with the Force global effect.
- Narrowing is the RIGHT projection of `queryReceipt.meaning`. Preservation uses that same iff with `forceReceipt.included` for the LEFT conjunct and the accepted input part for the RIGHT conjunct.

The old private `Leaf.of_parts` cannot be reused directly. The public structure assembly is small. `SharedTargetWorkerCompletion.force_complete` and `leaf_complete` then provide literal worker StableRun witnesses from the newly constructed exact graphs, without an old worker or range oracle.

## Profile-store review and boundaries

`SharedProfiles.Stored` keeps four independent obligations: native structure, native output profiles, Merge profiles, and immutable slot profile/height facts. `initial_stored` derives empty slots without a supplied result. `advance_stored` receives the two actual new native certificates. `physical_stored` uses unchanged native cells. `store_stored` requires the derived certificate for the exact new value and retains all other entries by put readback. `Stored.domain` correctly weakens to the prior structural invariant. These profile facts alone imply no heap availability, readiness, or semantic capture.

The class-wide scalar slot bound is appropriate when paired with old `Ready`, which ties each slot to this exact record and captured original forest. Do not replace `values` with currently edited siblings. Do not identify historical slot inventories with the current inventory. A new class can use `initial` to clear its local slots while retaining native and Merge tables.

Forcing can extend the unfolding memo. Only the subsequent native query retains its incoming global bundle identically. The final whole bundle must not be equated with the original bundle merely from native silence. Fourth-table correctness is retained through the existing public ForceReceipt and LeafReceipt `fourth_correct` lemmas by actual heap Keeps.

The full receipt's preservation law remains conditional on the captured forest language and ClassSat. It is not a supplied desired result. Constructor budgets do not count equality-operation tables, native tables, host memory, or elapsed time. These serial graph and literal worker endpoints retain the separate Haskell demand, pending-cell, and runtime correspondence boundaries.

An alternative adapter can derive the old ForceRanges via TargetInitialCapacity.target_capacity followed by the old target_ranges. It is honest but unnecessary for direct receipt construction. Deriving the old universal LeafRanges additionally requires alignment of every actual earlier Force with the constructed force; a single existential force return is not that universal premise.

No source file was edited and no build or Git operation was run for this review.
