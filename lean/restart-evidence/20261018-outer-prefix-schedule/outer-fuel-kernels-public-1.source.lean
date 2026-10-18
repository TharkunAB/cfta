import MicroCFTA.SourceCurrentOuterInitialFuel

set_option linter.all true

namespace MicroCFTA.OuterFuelKernels
open SourceCurrentOuterInitialFuel
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Seed" => List Guard × SourceCurrentAllocatedNativeResourceForecast.Profile
private def seed : Seed := ([⟨some [], .top⟩, ⟨some [[[0], [1]]], .top⟩], ⟨2,2,0,8⟩)
private noncomputable def firstParent := SourceCurrentOuterInitialSchedule.parent 0 seed
private noncomputable def rowTail := SourceCurrentOuterInitialSchedule.descendants 3 0 firstParent

/-- One initial ceiling covers a nested Parent and a later row Parent at distinct predicted entries. -/
theorem nested_and_tail :
    parentNeed 0 seed ≤ rowsNeed 4 0 seed ∧
    parentNeed 0 firstParent ≤ rowsNeed 4 0 seed ∧
    parentNeed 0 rowTail ≤ rowsNeed 4 0 seed := by
  have nested : parentNeed 0 firstParent ≤ nodeNeed 2 0 firstParent := by
    simpa only [nodeNeed,bodyNeed] using rows_parent_le 0 0 firstParent
  have entered : nodeNeed 2 0 firstParent ≤ descendantsNeed 3 0 firstParent := by
    simpa only [descendantsNeed,childrenNeed] using walk_node_le 2 0 firstParent
  have next : parentNeed 0 rowTail ≤ rowsNeed 3 0 rowTail := rows_parent_le 2 0 rowTail
  exact ⟨rows_parent_le 3 0 seed,
    Nat.le_trans (Nat.le_trans nested entered) (rows_descendants_le 3 0 seed),
    Nat.le_trans next (rows_tail_le 3 0 seed)⟩

end MicroCFTA.OuterFuelKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.OuterFuelKernels.nested_and_tail
#print MicroCFTA.OuterFuelKernels.nested_and_tail
#print axioms MicroCFTA.OuterFuelKernels.nested_and_tail
