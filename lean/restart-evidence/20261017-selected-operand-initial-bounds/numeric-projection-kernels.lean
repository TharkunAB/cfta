import MicroCFTA.SourceCurrentProjectionNumericControl

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.ProjectionNumericControlIntegration
open SourceCurrentProjectionNumericControl
open SourceCurrentProjectionUnionResources (headGrowth unionGrowth)

/-- Concrete rows use their exact successive scalars before the ordinary union. -/
theorem evaluated_rows :
    rowsStep (fun value => value + 1) 2 = 6 ∧
    rowsBound (fun value => value + 1) 3 2 = 30 ∧
    rowsBound (fun value => value + 1) 2 (rowsBound (fun value => value + 1) 1 2) = 30 ∧
    bound 0 7 = 8 ∧ ordinary (fun value => value + 1) 0 = 1 := by decide

/-- A shorter row prefix at an earlier scalar and its final union fit the direct ordinary branch. -/
theorem prefix_union_direct (depth current initial count : Nat)
    (counts : count ≤ initial) (resources : current ≤ initial) :
    current + count ≤ rowsBound (bound depth) count current ∧
      unionGrowth count (rowsBound (bound depth) count current) ≤ bound (depth + 1) initial := by
  have traversed := rowsBound_compare (fun enough => bound_mono depth enough)
    (fun _ => Nat.le_refl _) counts resources
  have united := SourceCurrentProjectionUnionResources.unionGrowth_mono counts traversed
  exact ⟨rowsBound_paid (bound depth) count current, Nat.le_trans united (ordinary_le_bound depth initial)⟩

/-- The same row-prefix proof after an actual head budget uses the same complete path envelope. -/
theorem prefix_union_after_head (depth initial count current : Nat)
    (counts : count ≤ headGrowth initial) (resources : current ≤ headGrowth initial) :
    headGrowth initial ≤ bound (depth + 1) initial ∧
      unionGrowth count (rowsBound (bound depth) count current) ≤ bound (depth + 1) initial ∧
      ordinary (bound depth) initial ≤ bound (depth + 1) initial := by
  have traversed := rowsBound_compare (fun enough => bound_mono depth enough)
    (fun _ => Nat.le_refl _) counts resources
  have united := SourceCurrentProjectionUnionResources.unionGrowth_mono counts traversed
  exact ⟨headGrowth_le_bound depth initial, united, ordinary_le_bound depth initial⟩

#print axioms evaluated_rows
#check @evaluated_rows
#print axioms prefix_union_direct
#check @prefix_union_direct
#print axioms prefix_union_after_head
#check @prefix_union_after_head
end MicroCFTA.ProjectionNumericControlIntegration
