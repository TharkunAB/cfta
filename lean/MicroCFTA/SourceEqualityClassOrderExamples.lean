import MicroCFTA.SourceEqualityClassOrder

/-!
# Coherent raw source classes with a comparator cycle

Each individual class has a valid trie and canonical path set. Their raw
combined payload is not normalized. Its comparator cycle makes the exact
source merge schedule relevant to physical order.
-/
namespace MicroCFTA.SourceEqualityClassOrderExamples
open SourceEqualityClassOrder

/-- The first raw class relates two supported paths at distinct child roots. -/
def first : Record := ⟨.branch [(0, .terminal), (1, .branch [(0, .terminal)])], [[0], [1, 0]]⟩

/-- The second raw class continues the strict-prefix cycle. -/
def second : Record := ⟨.branch [(1, .terminal), (2, .branch [(0, .terminal)])], [[1], [2, 0]]⟩

/-- The third raw class completes the strict-prefix cycle. -/
def third : Record := ⟨.branch [(0, .branch [(0, .terminal)]), (2, .terminal)], [[0, 0], [2]]⟩

/-- Every raw class has coherent physical fields despite the combined comparator cycle. -/
theorem coherent_records : Coherent first ∧ Coherent second ∧ Coherent third := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    refine ⟨by simp [first, second, third, EqualityTrie.Valid, or_imp, forall_and], by cbv, ?_⟩
    intro path
    rfl

/-- Raw coherent source classes do not make completedSubsumptionOrdering transitive. -/
theorem raw_cycle : completedCompare first third = .lt ∧ completedCompare third second = .lt ∧ completedCompare second first = .lt := by
  decide +kernel

/-- The source three-item merge order differs from a right-associated finite merge on this raw input. -/
theorem merge_schedule_matters :
    (ordered [first, second, third]).map Record.paths = [third.paths, second.paths, first.paths] ∧
      (SourceListSort.merge (fun left right => completedCompare left right == .gt) [first]
        (SourceListSort.merge (fun left right => completedCompare left right == .gt) [second] [third])).map Record.paths =
          [first.paths, third.paths, second.paths] := by
  decide +kernel

end MicroCFTA.SourceEqualityClassOrderExamples
