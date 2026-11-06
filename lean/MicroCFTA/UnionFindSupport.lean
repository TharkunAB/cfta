import MicroCFTA.UnionFind

namespace MicroCFTA.UnionFindSupport

open MicroCFTA.UnionFind

/-- The forest has no stored entries at or above `bound`. -/
def SupportedBelow (bound : Nat) (forest : Forest) : Prop :=
  ∀ key, bound ≤ key → forest key = none

/-- The empty forest has no stored entries. -/
theorem supportedBelow_empty : SupportedBelow 0 (fun _ => none) := by
  intro key _
  rfl

/-- One write preserves a bound computed from the old bound and the key. -/
theorem supportedBelow_write {bound : Nat} {forest : Forest}
    (h : SupportedBelow bound forest) (key : Nat) (entry : Option Entry) :
    SupportedBelow (max bound (key + 1))
      (fun index => if index = key then entry else forest index) := by
  intro index hindex
  have hne : index ≠ key := by omega
  simpa [hne] using h index (Nat.le_trans (Nat.le_max_left _ _) hindex)

end MicroCFTA.UnionFindSupport
