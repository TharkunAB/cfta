import MicroCFTA.EqualityLeafProjectionRows
import MicroCFTA.SourceCompactGuards

/-!
# Source admission of canonical leaf guards

A leaf with empty stored equalities survives source arity checking when its
residual is Top or is not a positive equality conjunction. This property is
closed under source conjunction. Literal Bottom rejection is handled by the
non-Bottom row carrier.
-/
namespace MicroCFTA.EqualityLeafProjectionAdmission
open SourceGuards FullSyntax GuardConjunction SourceCompactGuards

/-- The positive-equality list fold succeeds exactly when both parts succeed. -/
theorem positive_cons (guard : Guard Formula) (guards : List (Guard Formula)) :
    (positiveList (guard :: guards)).isSome = true ↔
      (positive guard).isSome = true ∧ (positiveList guards).isSome = true := by
  cases first : positive guard <;> cases rest : positiveList guards <;> simp [positiveList, first, rest]

mutual
  /-- Positive equality extraction depends only on the flattened outer atoms. -/
  theorem positive_atoms (guard : Guard Formula) :
      (positive guard).isSome = true ↔ ∀ atom ∈ atoms guard, (positive atom).isSome = true := by
    cases guard with
    | top => simp [positive, atoms]
    | and guards => simpa only [positive, atoms] using positive_atoms_list guards
    | bottom | same | entails | satisfies | holds | substitute | not | or => simp only [atoms, List.mem_singleton, forall_eq]

  /-- Source outer flattening preserves the all-positive list test. -/
  theorem positive_atoms_list (guards : List (Guard Formula)) :
      (positiveList guards).isSome = true ↔ ∀ atom ∈ guards.flatMap atoms, (positive atom).isSome = true := by
    cases guards with
    | nil => simp [positiveList]
    | cons guard rest =>
        rw [positive_cons, positive_atoms guard, positive_atoms_list rest]
        simp only [List.flatMap_cons, List.mem_append]
        constructor
        · rintro ⟨first, tail⟩ atom (left | right)
          · exact first atom left
          · exact tail atom right
        · intro all
          exact ⟨fun atom member => all atom (Or.inl member), fun atom member => all atom (Or.inr member)⟩
end

/-- Canonical conjunction retains every non-positive outer residual atom. -/
theorem positive_merge (first second : Guard Formula) :
    (positive (merge GuardStructuralOrder.le first second)).isSome = true ↔
      (positive first).isSome = true ∧ (positive second).isSome = true := by
  rw [positive_atoms, positive_atoms, positive_atoms]
  constructor
  · intro all
    exact ⟨fun atom member => all atom ((merge_mem _ _ _ _).mpr (Or.inl member)),
      fun atom member => all atom ((merge_mem _ _ _ _).mpr (Or.inr member))⟩
  · rintro ⟨left, right⟩ atom member
    exact (merge_mem _ _ _ _).mp member |>.elim (left atom) (right atom)

/-- A leaf has no extracted positive equality path that can fail arity zero. -/
def NoLeafEquality (guard : Guard Formula) : Prop := (positive guard).isSome = false ∨ guard = .top

/-- Source conjunction preserves the zero-arity equality condition. -/
theorem merge_noLeafEquality (first second : Guard Formula)
    (left : NoLeafEquality first) (right : NoLeafEquality second) :
    NoLeafEquality (merge GuardStructuralOrder.le first second) := by
  rcases left with left | rfl
  · left
    cases found : (positive (merge GuardStructuralOrder.le first second)).isSome
    · rfl
    · have impossible := (positive_merge first second).mp found
      simp [left] at impossible
  · rcases right with right | rfl
    · left
      cases found : (positive (merge GuardStructuralOrder.le .top second)).isSome
      · rfl
      · have impossible := (positive_merge .top second).mp found
        simp [right] at impossible
    · right
      simp [merge, GuardConjunction.normalize, atoms, canonical, conjoin]

/-- Actual staged equality extraction returns only the stored empty equality field. -/
theorem source_equalities (guard : Guard Formula) (admitted : NoLeafEquality guard) :
    sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard) = some [] := by
  rcases admitted with residual | rfl
  · have support := positiveNormalized_support guard
    have none : positiveNormalized guard = none := by
      cases found : positiveNormalized guard with
      | none => rfl
      | some classes => simp [found, residual] at support
    simp only [sourceEqualities, none]
  · rfl

/-- This leaf row survives both literal Bottom rejection and positive-equality arity checking. -/
def Row (initial : List (Guard Formula)) :=
  {row : EqualityLeafProjectionRows.Row initial // NoLeafEquality row.val.val}

/-- Canonical source row conjunction preserves physical leaf admission. -/
def join (initial : List (Guard Formula)) (first second : Row initial) : Row initial :=
  ⟨EqualityLeafProjectionRows.join initial first.val second.val,
    merge_noLeafEquality first.val.val.val second.val.val.val first.property second.property⟩

/-- The admitted row carrier retains the exact source conjunction algebra. -/
def algebra (initial : List (Guard Formula)) : FiniteRowIntersection.Conjunction (Row initial) where
  join := join initial
  assoc := fun first second third => Subtype.ext ((EqualityLeafProjectionRows.algebra initial).assoc first.val second.val third.val)
  comm := fun first second => Subtype.ext ((EqualityLeafProjectionRows.algebra initial).comm first.val second.val)
  idem := fun first => Subtype.ext ((EqualityLeafProjectionRows.algebra initial).idem first.val)

/-- Generate the admitted physical row inventory from the original finite atom subsets. -/
noncomputable def inventory (initial : List (Guard Formula)) : List (Row initial) := by
  classical
  exact (EqualityLeafProjectionRows.inventory initial).filterMap fun row =>
    if admitted : NoLeafEquality row.val.val then some ⟨row, admitted⟩ else none

/-- The second constructor-admission filter retains every admitted residual. -/
theorem inventory_complete (initial : List (Guard Formula)) (row : Row initial) : row ∈ inventory initial := by
  unfold inventory
  apply List.mem_filterMap.mpr
  refine ⟨row.val, EqualityLeafProjectionRows.inventory_complete initial row.val, ?_⟩
  rw [dite_eq_left row.property]
  exact congrArg some (Subtype.ext rfl)

/-- Physical admission keeps the original derived finite inventory bound. -/
theorem inventory_length (initial : List (Guard Formula)) :
    (inventory initial).length ≤ 2 ^ (SourceLeafRowProgress.basis initial).length :=
  Nat.le_trans (List.length_filterMap_le _ _) (EqualityLeafProjectionRows.inventory_length initial)

/-- Every admitted guard has exact empty source equalities on a nullary edge. -/
theorem row_equalities (initial : List (Guard Formula)) (row : Row initial) :
    sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) row.val.val.val) = some [] :=
  source_equalities row.val.val.val row.property

/-- No admitted physical row is removed by literal Bottom rejection. -/
theorem row_ne_bottom (initial : List (Guard Formula)) (row : Row initial) : row.val.val.val ≠ .bottom :=
  row.val.property

end MicroCFTA.EqualityLeafProjectionAdmission
