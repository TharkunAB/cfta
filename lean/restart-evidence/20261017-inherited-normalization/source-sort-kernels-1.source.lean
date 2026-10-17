import MicroCFTA.SourceListSortOrdered

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.SourceSortKernels
open SourceListSort EqualityTrie EqualityNormalize SourceEqualityClassOrder

private def gt (a b : Nat) : Bool := decide (b < a)
private def five : List Nat := [7, 8, 5, 6, 3, 4, 1, 2]
private def six : List Nat := [9, 10, 7, 8, 5, 6, 3, 4, 1, 2]
private def seven : List Nat := [9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 0, 0]

/-- The actual five-run, six-run, and longer schedules sort mixed ascending runs and retain ties. -/
theorem special_run_schedules :
    (sequences gt five).length = 5 ∧ (sequences gt six).length = 6 ∧
    (sequences gt seven).length = 7 ∧
    actualSort gt five = [1, 2, 3, 4, 5, 6, 7, 8] ∧
    actualSort gt six = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] ∧
    actualSort gt seven = [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] ∧
    (actualSort gt seven).Pairwise (· ≤ ·) := by
  have chosen : ∀ a b : Nat, if gt a b then b ≤ a else a ≤ b := by
    intro a b
    by_cases less : b < a
    · simpa [gt, less] using Nat.le_of_lt less
    · simp only [gt, less, decide_false, Bool.false_eq_true, ite_false]
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · exact SourceListSortOrdered.actualSort_ordered (· ≤ ·) gt Nat.le_trans chosen seven

private def high : Record := ⟨.branch [(2, .terminal), (3, .terminal)], [[2], [3]]⟩
private def low : Record := ⟨.branch [(0, .terminal), (1, .terminal)], [[0], [1]]⟩

/-- Actual constructed records sort by path sets with complete repeated records retained. -/
theorem physical_records :
    recordsOf [[[2], [3]], [[0], [1]], [[2], [3]]] = some [high, low, high] ∧
    sortBy (fun a b : Record => compare a.paths b.paths) [high, low, high] = [low, high, high] ∧
    (sortBy (fun a b : Record => compare a.paths b.paths) [high, low, high]).Pairwise
      (fun a b => a.paths ≤ b.paths) := by
  refine ⟨?_, ?_, SourceListSortOrdered.paths _⟩
  · cbv
  · cbv

end MicroCFTA.SourceSortKernels
