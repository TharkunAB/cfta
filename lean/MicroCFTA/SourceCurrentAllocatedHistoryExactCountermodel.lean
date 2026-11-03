import MicroCFTA.SourcePruningEnumerationCachedChild

/-! The allocation history need not equal the original active list. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentAllocatedHistoryExactCountermodel
open EnumerationState
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}

/-- A duplicate active key disproves the rejected primitive equality. -/
theorem duplicated_active_countermodel (seed : EnumerationState.State Symbol Guard) :
    let key := recursionKey 0 []
    let before : EnumerationState.State Symbol Guard :=
      {seed with counter := 0, expansionAncestry := [key, key], recursionAncestry := fun _ => []}
    (allocated none before).recursionAncestry before.counter ≠ before.expansionAncestry := by
  simp [EnumerationState.allocated, List.eraseDups_cons]

end MicroCFTA.SourceCurrentAllocatedHistoryExactCountermodel
