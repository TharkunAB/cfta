import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds

/-!
# Profiles through actual merge selection and group traversal

Selection returns only original values and cannot increase multiplicity.
The threshold branches return no more rows than their original group.
These facts follow the supplied actual completed graph. They do not supply
profiles for recursive merge results or assert their completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual selection retains only source values and cannot increase their number. -/
theorem selected_inputs (clear : Guard → Bool) (fuel : Nat)
    (inputs values : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done values after) :
    (∀ value ∈ values, value ∈ inputs) ∧ values.length ≤ inputs.length := by
  obtain ⟨retained, middle, filtered, returned⟩ := (SourceMergedComparisonEffects.bind_done _ _ values after).mp done
  obtain ⟨rfl, rfl⟩ := MergedSourceComparison.Result.done.inj returned
  have inside := (SourceMergedSelection.retain_members clear fuel
    (inputs.filter MergedPhysicalGroupColumns.closedMu) inputs before retained _ filtered).1
  have selected : ∀ value ∈ distinctNodes retained, value ∈ inputs :=
    fun value member => inside value (distinctNodes_member _ value member)
  refine ⟨selected, ?_⟩
  have bound := (InternedNonemptyRecords.distinctNodes_nodup retained).length_le_of_subset (l₂ := inputs.map Value.referenceOf) (by
    intro reference member
    obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨value, selected value present, rfl⟩)
  simpa only [List.length_map] using bound

/-- The exact selected list retains the complete original uniform profile. -/
theorem selected_profile (clear : Guard → Bool) (fuel : Nat)
    (inputs values : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done values after)
    (rows arity : Nat) (profile : ChildrenShape rows arity inputs) :
    ChildrenShape rows arity values ∧ values.length ≤ inputs.length := by
  have selected := selected_inputs clear fuel inputs values before after done
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.children_of_members values
    (fun value member => ChildrenShape.member inputs profile value (selected.1 value member)), selected.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Ordinary retained columns exclude the source explicit recursive-union branch. -/
theorem retained_column (inputs : List (Value Symbol Guard)) (rows arity : Nat)
    (profile : ChildrenShape rows arity inputs) :
    retainedColumn inputs = match inputs with
      | [single] => .pure single
      | others => .bind (.work (MergedOrdinaryHeight.ordinaryUnion others)) Code.request := by
  have ordinary : inputs.any MergedOrdinaryHeight.recursiveBoundary = false := List.any_eq_false.mpr (by
    intro value member
    have domain := NodeShape.domain value (ChildrenShape.member inputs profile value member)
    cases domain <;> simp [MergedOrdinaryHeight.recursiveBoundary])
  cases inputs with
  | nil => simp [retainedColumn, ordinary]
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => simp only [retainedColumn, ordinary, Bool.false_eq_true, ite_false]

/-- Actual ordered graph traversal retains the number of source occurrences. -/
theorem map_length {clear : Guard → Bool} {top : Guard} {call : Input → Code Symbol Guard Output}
    {inputs : List Input} {values : List Output} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard}
    (actual : Run clear top (map call inputs) before memo values after saved) : values.length = inputs.length := by
  induction inputs generalizing before memo values with
  | nil => have same := (Run.pure_iff.mp actual).1; subst values; rfl
  | cons first rest ih =>
      obtain ⟨value, tail, middle, current, _head, later, rfl⟩ := Run.map_cons_iff.mp actual
      exact congrArg Nat.succ (ih later)

/-- Each actual threshold branch returns no more rows than its source group. -/
theorem group_length {clear : Guard → Bool} {top : Guard} {edges values : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (group top edges) before memo values after saved) : values.length ≤ edges.length := by
  unfold group at actual
  split at actual
  · exact Nat.le_of_eq (map_length actual)
  · cases edges with
    | nil => have same := (Run.pure_iff.mp actual).1; subst values; exact Nat.le_refl _
    | cons first rest =>
        obtain ⟨value, middle, current, _large, pure⟩ := Run.bind_iff.mp actual
        have same := (Run.pure_iff.mp pure).1
        subst values
        simp

/-- Actual ordered group results cannot add alternatives before the final node filter. -/
theorem groups_length {clear : Guard → Bool} {top : Guard}
    {groups : List (List (EdgeValue Symbol Guard))} {values : List (List (EdgeValue Symbol Guard))}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (map (group top) groups) before memo values after saved) :
    values.flatten.length ≤ groups.flatten.length := by
  induction groups generalizing before memo values with
  | nil => have same := (Run.pure_iff.mp actual).1; subst values; exact Nat.le_refl _
  | cons first rest ih =>
      obtain ⟨value, tail, middle, current, head, later, rfl⟩ := Run.map_cons_iff.mp actual
      simpa only [List.flatten_cons, List.length_append] using Nat.add_le_add (group_length head) (ih later)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection
