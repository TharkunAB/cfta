import MicroCFTA.SourceListSortRunsOrdered
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
namespace MicroCFTA.SourceSortRunsKernels
private def input : List Nat := [5,4,3,7,8,6,6,2,1,9]
private def greater (a b : Nat) : Bool := decide (b < a)
/-- Actual source detection retains descending reversal, ascending runs, repeated values, and the final singleton. -/
theorem actual_mixed_runs :
    SourceListSort.sequences greater input = [[3,4,5],[7,8],[6,6],[1,2],[9]] ∧
    ∀ run ∈ SourceListSort.sequences greater input, run.Pairwise (· ≤ ·) := by
  refine ⟨by cbv, ?_⟩
  apply SourceListSortRunsOrdered.sequences_ordered (fun a b : Nat => a ≤ b) greater
    (fun first second => Nat.le_trans first second)
  intro a b
  split
  · rename_i choice
    have before : b < a := by simpa only [greater, decide_eq_true_eq] using choice
    omega
  · rename_i choice
    have before : ¬ b < a := by simpa only [greater, decide_eq_true_eq] using choice
    omega
end MicroCFTA.SourceSortRunsKernels
#check @MicroCFTA.SourceSortRunsKernels.actual_mixed_runs
#print MicroCFTA.SourceSortRunsKernels.actual_mixed_runs
#print axioms MicroCFTA.SourceSortRunsKernels.actual_mixed_runs
