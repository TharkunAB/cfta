import MicroCFTA.SourcePlanPartition
import MicroCFTA.CompactGroups

/-!
# Positive PlanScale and repeated child sizes

The source scales class-count keys and divides the requested selector size.
The raw selector does not test divisibility. A valid counted class supplies
that test. Positive scaling preserves ordinary ranks, class ranks, and
selected values. A group of equal children supplies a positive factor.
-/

namespace MicroCFTA.SourcePlanScale

open SourcePlanPositions SourcePlanPartition SizedRank Language RecursiveSize

/-- Positive scaling preserves the ordinary cardinality. -/
theorem count_scale (factor : Nat) (positive : 0 < factor) (plan : Plan) :
    count (.scale factor positive plan) = count plan := rfl

/-- Scaling a valid size retains the entire class in its original order. -/
theorem class_scale (factor : Nat) (positive : 0 < factor) (plan : Plan) (size : Nat) :
    classRanks (.scale factor positive plan) (factor * size) = classRanks plan size := by
  simp [classRanks, Nat.mul_div_cancel_left size positive]

/-- A nondivisible size has no members in the scaled count table. -/
theorem class_absent (factor : Nat) (positive : 0 < factor) (plan : Plan) (size : Nat)
    (nondivisible : size % factor ≠ 0) :
    classRanks (.scale factor positive plan) size = [] := by simp [classRanks, nondivisible]

/-- Every valid scaled class position has a divisible size. -/
theorem counted_size_divisible (factor : Nat) (positive : 0 < factor) (plan : Plan)
    (part : Position) (valid : part.rank < (classRanks (.scale factor positive plan) part.size).length) :
    part.size % factor = 0 := by
  by_cases divisible : part.size % factor = 0
  · exact divisible
  · rw [class_absent factor positive plan part.size divisible] at valid
    simp at valid

/-- Source position conversion multiplies only the member size. -/
theorem position_scale (factor : Nat) (positive : 0 < factor) (plan : Plan)
    (rank : Nat) (part : Position) (found : position plan rank = some part) :
    position (.scale factor positive plan) rank = some ⟨factor * part.size, part.rank⟩ := by
  simp [position, found]

/-- The source scaleIndex selector divides the size without a separate check. -/
def sourceSelect (factor : Nat) (plan : Plan) (select : Nat → Option Value)
    (part : Position) : Option Value :=
  selectClass plan select ⟨part.size / factor, part.rank⟩

/-- On counted class positions, raw source selection agrees with exact class lookup. -/
theorem sourceSelect_valid (factor : Nat) (positive : 0 < factor) (plan : Plan)
    (select : Nat → Option Value) (part : Position)
    (valid : part.rank < (classRanks (.scale factor positive plan) part.size).length) :
    sourceSelect factor plan select part = selectClass (.scale factor positive plan) select part := by
  have divisible := counted_size_divisible factor positive plan part valid
  simp [sourceSelect, selectClass, classRanks, divisible]

/-- The source selector preserves every value at its scaled class position. -/
theorem sourceSelect_scaled (factor : Nat) (positive : 0 < factor) (plan : Plan)
    (select : Nat → Option Value) (part : Position) :
    sourceSelect factor plan select ⟨factor * part.size, part.rank⟩ = selectClass plan select part := by
  simp [sourceSelect, Nat.mul_div_cancel_left part.size positive]

/-- A valid ordinary member retains its value and class rank after scaling. -/
theorem member_value_preserved (factor : Nat) (positive : 0 < factor) (plan : Plan)
    (select : Nat → Option Value) (rank : Nat) (part : Position) (value : Value)
    (found : position plan rank = some part) (selected : select rank = some value) :
    sourceSelect factor plan select ⟨factor * part.size, part.rank⟩ = some value := by
  rw [sourceSelect_scaled factor positive plan select part]
  simp [selectClass, position_replay plan rank part found, selected]

/-- The maximum possible member size is multiplied by the same factor. -/
theorem maxSize_scale (factor : Nat) (positive : 0 < factor) (plan : Plan) :
    maxSize (.scale factor positive plan) = factor * maxSize plan := rfl

/-- Repeating a child at several positions adds its node count at every position. -/
theorem repeated_child_nodes (term : Term Symbol) (multiplicity : Nat) :
    forestSize (List.replicate multiplicity term) = multiplicity * nodeSize term := by
  induction multiplicity with
  | zero => simp [forestSize]
  | succ multiplicity ih =>
      simp only [List.replicate_succ]
      change nodeSize term + forestSize (List.replicate multiplicity term) =
        (multiplicity + 1) * nodeSize term
      rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- The source grouping invariant supplies the positive PlanScale factor. -/
theorem group_factor_positive (arity : Nat) (equalities : List (List Nat))
    (valid : CompactGroups.ValidClasses arity equalities) (positions : List Nat)
    (member : positions ∈ CompactGroups.childGroups arity equalities) :
    0 < positions.length := by
  have nonempty := CompactGroups.childGroups_nonempty arity equalities valid positions member
  exact Nat.pos_of_ne_zero (fun zero => nonempty (List.length_eq_zero_iff.mp zero))

/-- Scale one shared child by the number of positions in its checked group. -/
def groupPlan (arity : Nat) (equalities : List (List Nat))
    (valid : CompactGroups.ValidClasses arity equalities) (positions : List Nat)
    (member : positions ∈ CompactGroups.childGroups arity equalities) (plan : Plan) : Plan :=
  .scale positions.length (group_factor_positive arity equalities valid positions member) plan

/-- A shared child contributes the node count of all its reconstructed occurrences. -/
theorem group_position_nodes (arity : Nat) (equalities : List (List Nat))
    (valid : CompactGroups.ValidClasses arity equalities) (positions : List Nat)
    (member : positions ∈ CompactGroups.childGroups arity equalities)
    (plan : Plan) (rank : Nat) (part : Position) (term : Term Symbol)
    (found : position plan rank = some part) (sized : part.size = nodeSize term) :
    position (groupPlan arity equalities valid positions member plan) rank =
      some ⟨forestSize (List.replicate positions.length term), part.rank⟩ := by
  rw [groupPlan, position_scale positions.length _ plan rank part found,
    repeated_child_nodes, sized]

/-- The factor-one smart-constructor shortcut preserves every class. -/
theorem class_scale_one (plan : Plan) (size : Nat) :
    classRanks (.scale 1 (by decide) plan) size = classRanks plan size := by
  simp [classRanks, Nat.mod_one]

/-- The factor-one shortcut preserves every position result. -/
theorem position_scale_one (plan : Plan) (rank : Nat) :
    position (.scale 1 (by decide) plan) rank = position plan rank := by
  cases found : position plan rank <;> simp [position, found]

/-- A raw selector can return a value at an uncounted nondivisible size.
Callers must establish the counted-class premise before raw selection. -/
theorem raw_selection_needs_counted_size :
    sourceSelect 2 (.select 1) (fun rank => if rank = 0 then some 7 else none) ⟨3, 0⟩ = some 7 ∧
      classRanks (.scale 2 (by decide) (.select 1)) 3 = [] := by
  decide

end MicroCFTA.SourcePlanScale
