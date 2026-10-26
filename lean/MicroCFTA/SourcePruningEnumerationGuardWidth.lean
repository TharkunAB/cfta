import MicroCFTA.SourcePruningEnumerationConstraint

/-!
# Equality-class widths from an initial finite guard alphabet

The alphabet bounds each successful constraint projection. The sum retains
duplicate entries. Unsupported projections contribute zero to this bound.
No future heap, successful execution or normalized-payload premise is needed.
-/
namespace MicroCFTA.SourcePruningEnumerationGuardWidth
variable {Formula : Type}

/-- Count the equality tries returned by one actual supported projection. -/
noncomputable def projectedWidth (constraint : SourceSymbolicIndex.Constraint Formula) : Nat :=
  match SourcePruningEnumerationConstraint.project constraint with
  | none => 0
  | some (tries, _) => tries.length

/-- Sum the projection widths of the original finite guard alphabet. -/
noncomputable def width (alphabet : List (SourceSymbolicIndex.Constraint Formula)) : Nat :=
  (alphabet.map projectedWidth).sum

/-- Membership in the original alphabet bounds one guard's projection width. -/
theorem width_member (alphabet : List (SourceSymbolicIndex.Constraint Formula))
    (constraint : SourceSymbolicIndex.Constraint Formula) (member : constraint ∈ alphabet) :
    projectedWidth constraint ≤ width alphabet := by
  unfold width
  induction alphabet with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp only [List.map_cons, List.sum_cons]
        omega
      · have lower := ih later
        simp only [List.map_cons, List.sum_cons]
        omega

/-- An actual successful projection needs no supplied bound on its returned tries. -/
theorem project_le (alphabet : List (SourceSymbolicIndex.Constraint Formula))
    (constraint : SourceSymbolicIndex.Constraint Formula)
    (tries : List EqualityTrie.Trie) (residual : Option (SourceSymbolicIndex.Constraint Formula))
    (member : constraint ∈ alphabet)
    (projected : SourcePruningEnumerationConstraint.project constraint = some (tries, residual)) :
    tries.length ≤ width alphabet := by
  have bound := width_member alphabet constraint member
  simpa only [projectedWidth, projected] using bound

end MicroCFTA.SourcePruningEnumerationGuardWidth
