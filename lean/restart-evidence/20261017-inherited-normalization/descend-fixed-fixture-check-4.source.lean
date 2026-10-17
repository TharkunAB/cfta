import MicroCFTA.SourceCurrentEqualityNormalizationFixed
import MicroCFTA.SourceEqualityInheritedPayload
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.DescendFixedKernels
open EqualityNormalize SourceEqualityClassOrder SourceEqualityDescend
open SourceCurrentEqualityNormalizationFixed
private def getRecord (paths : Class) : Record := (recordOf paths).getD ⟨.empty,[]⟩
private theorem actual_normalize (fuel : Nat) (input output : Constraints)
    (done : mkEqConstraints fuel input = .normalized output) : SourceCompactGuards.normalize input = some output := by
  have exact := SourceEqualityNormalizationReceipt.array_eq fuel input (by rw [done]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [exact,done]
  rfl
private theorem physical_wellFormed (classes : Constraints) (originals : List Record)
    (fixed : Fixed classes) (built : recordsOf classes = some originals) : WellFormed (some originals) := by
  have known := invariants classes fixed
  have normal := EqualitySaturation.step_normal classes classes known.1 known.2.2.2
  have cached : SourceEqualityGuardReadback.Cached (some classes) := by
    intro values same
    cases same
    exact ⟨known.1,known.2.1,normal.2.2.2⟩
  apply SourceEqualityInheritedPayload.read_wellFormed (some classes) cached
  simp only [SourceEqualityPhysicalPayload.read,built]
private def raw : Constraints := [[[1,6],[0,9],[1,5]],[[1,1],[1,0],[0,10]]]
private def sorted : Constraints := [[[0,9],[1,5],[1,6]],[[0,10],[1,0],[1,1]]]
private def originals : List Record := [getRecord [[0,9],[1,5],[1,6]],getRecord [[0,10],[1,0],[1,1]]]
private def child := records 1 originals
private theorem sorted_actual : SourceCompactGuards.normalize raw = some sorted :=
  actual_normalize 3 raw sorted (by cbv)
private theorem sorted_fixed : Fixed sorted := normalize_idempotent raw sorted sorted_actual
private theorem originals_built : recordsOf sorted = some originals := by cbv
private theorem originals_paths : originals.map Record.paths = sorted := by cbv
private theorem originals_good : WellFormed (some originals) := physical_wellFormed sorted originals sorted_fixed originals_built
/-- Actual source normalization and physical trie descent reorder two retained classes and retain exact normalization fixedness. -/
theorem actual_reordered_descent :
    SourceCompactGuards.normalize raw = some sorted ∧
    recordsOf sorted = some originals ∧ WellFormed (some originals) ∧
    descend (some originals) 1 = some child ∧ child.map Record.paths = [[[0],[1]],[[5],[6]]] ∧
    Fixed (child.map Record.paths) ∧
    SourceCompactGuards.normalize (child.map Record.paths) = some (child.map Record.paths) := by
  have childFixed : Fixed (child.map Record.paths) := of_step _ (by
    have paths : child.map Record.paths = [[[0],[1]],[[5],[6]]] := by cbv
    rw [paths]
    unfold Active Nontrivial
    decide) (by cbv)
  exact ⟨sorted_actual,originals_built,originals_good,rfl,by cbv,childFixed,childFixed⟩
private def rawNested : Constraints := [[[2,1],[2,0]],[[2,2],[2,0,3]]]
private def closedNested : Constraints := [[[2,0],[2,1]],[[2,0,3],[2,1,3],[2,2]]]
private def nestedOriginals : List Record := [getRecord [[2,0],[2,1]],getRecord [[2,0,3],[2,1,3],[2,2]]]
private def nestedChild := records 2 nestedOriginals
private theorem nested_actual : SourceCompactGuards.normalize rawNested = some closedNested :=
  actual_normalize 4 rawNested closedNested (by cbv)
private theorem nested_fixed : Fixed closedNested := normalize_idempotent rawNested closedNested nested_actual
private theorem nested_built : recordsOf closedNested = some nestedOriginals := by cbv
private theorem nested_paths : nestedOriginals.map Record.paths = closedNested := by cbv
private theorem nested_good : WellFormed (some nestedOriginals) := physical_wellFormed closedNested nestedOriginals nested_fixed nested_built
/-- A source-generated suffix congruence survives actual trie descent, and a later empty descent remains exactly fixed. -/
theorem actual_generated_suffix_descent :
    SourceCompactGuards.normalize rawNested = some closedNested ∧
    recordsOf closedNested = some nestedOriginals ∧ WellFormed (some nestedOriginals) ∧
    descend (some nestedOriginals) 2 = some nestedChild ∧
    nestedChild.map Record.paths = [[[0],[1]],[[0,3],[1,3],[2]]] ∧
    Fixed (nestedChild.map Record.paths) ∧
    descend (some nestedChild) 0 = some [] ∧ Fixed ([] : Constraints) := by
  have childFixed : Fixed (nestedChild.map Record.paths) := of_step _ (by
    have paths : nestedChild.map Record.paths = [[[0],[1]],[[0,3],[1,3],[2]]] := by cbv
    rw [paths]
    unfold Active Nontrivial
    decide) (by cbv)
  have empty : Fixed ((records 0 nestedChild).map Record.paths) := of_step _ (by
    have paths : (records 0 nestedChild).map Record.paths = [] := by cbv
    rw [paths]
    simp [Active]) (by cbv)
  have paths : (records 0 nestedChild).map Record.paths = [] := by cbv
  exact ⟨nested_actual,nested_built,nested_good,rfl,by cbv,childFixed,by cbv,paths ▸ empty⟩
end MicroCFTA.DescendFixedKernels
#check @MicroCFTA.DescendFixedKernels.actual_reordered_descent
#print axioms MicroCFTA.DescendFixedKernels.actual_reordered_descent
#check @MicroCFTA.DescendFixedKernels.actual_generated_suffix_descent
#print axioms MicroCFTA.DescendFixedKernels.actual_generated_suffix_descent
