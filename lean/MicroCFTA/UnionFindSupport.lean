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

/-- An actual write preserves the computed support bound. -/
theorem supportedBelow_put {bound : Nat} {forest : Forest}
    (supported : SupportedBelow bound forest) (key : Nat) (entry : Entry) :
    SupportedBelow (max bound (key + 1)) (put forest key entry) := by
  intro index beyond
  have unequal : index ≠ key := by omega
  simpa [put, unequal, Ne.symm unequal] using
    supported index (Nat.le_trans (Nat.le_max_left _ _) beyond)

/-- Compute an exclusive bound for the listed variables. -/
def initialBound : List Nat → Nat
  | [] => 0
  | key :: rest => max (key + 1) (initialBound rest)

/-- Each listed variable is below the computed bound. -/
theorem lt_initialBound_of_mem (variables : List Nat) :
    ∀ key, key ∈ variables → key < initialBound variables := by
  induction variables with
  | nil =>
      intro key member
      cases member
  | cons first rest inductionHypothesis =>
      intro key member
      cases member with
      | head =>
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self first) (Nat.le_max_left _ _)
      | tail _ member =>
          exact Nat.lt_of_lt_of_le (inductionHypothesis key member) (Nat.le_max_right _ _)

/-- Initialization has a bound computed from its input list. -/
theorem supportedBelow_withInitialValues (variables : List Nat) :
    SupportedBelow (initialBound variables) (withInitialValues variables) := by
  intro key beyond
  have absent : key ∉ variables := by
    intro member
    have small := lt_initialBound_of_mem variables key member
    omega
  simp [withInitialValues, absent]

end MicroCFTA.UnionFindSupport
