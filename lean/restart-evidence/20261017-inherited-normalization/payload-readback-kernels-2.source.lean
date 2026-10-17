import MicroCFTA.SourceCurrentEqualityPayloadReadback

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.PayloadReadbackKernels
open EqualityTrie EqualityNormalize SourceEqualityClassOrder

private def high : Record := ⟨.branch [(2, .terminal), (3, .terminal)], [[2], [3]]⟩
private def low : Record := ⟨.branch [(0, .terminal), (1, .terminal)], [[0], [1]]⟩
private theorem highBuilt : recordOf [[2], [3]] = some high := by cbv
private theorem lowBuilt : recordOf [[0], [1]] = some low := by cbv

private theorem recordFacts (paths : Class) (value : Record)
    (supported : Supported paths.eraseDups) (actual : recordOf paths = some value) :
    Coherent value ∧ Ascending value.trie := by
  obtain ⟨result, built, coherent, _⟩ := recordOf_complete paths supported
  have same := Option.some.inj (built.symm.trans actual)
  cases same
  exact ⟨coherent, SourceEqualityDescend.recordOf_ascending paths value actual⟩

/-- Actual record construction and readback retain an unsorted repeated class list. -/
theorem repeated_order :
    recordsOf [[[2], [3]], [[0], [1]], [[2], [3]]] = some [high, low, high] ∧
    SourceEqualityDescend.WellFormed (some [high, low, high]) ∧
    SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes (some [high, low, high])) =
      .ok (some [high, low, high]) ∧ high.paths ≠ low.paths := by
  have first := recordFacts [[2], [3]] high (by simp [Supported]) highBuilt
  have second := recordFacts [[0], [1]] low (by simp [Supported]) lowBuilt
  have wf : SourceEqualityDescend.WellFormed (some [high, low, high]) := by
    intro originals same value member
    cases same
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨first.1, first.2, [2], by simp [high], [3], by simp [high], by decide⟩
    · exact ⟨second.1, second.2, [0], by simp [low], [1], by simp [low], by decide⟩
    · exact ⟨first.1, first.2, [2], by simp [high], [3], by simp [high], by decide⟩
  refine ⟨?_, wf, SourceCurrentEqualityPayloadReadback.read _ wf, by decide⟩
  simp only [recordsOf, highBuilt, lowBuilt, Option.bind_some]
  rfl

private def reversed : Record := ⟨.branch [(1, .terminal), (0, .terminal)], [[0], [1]]⟩

/-- Coherence alone permits a different physical trie order, which actual readback changes. -/
theorem ascending_boundary :
    Coherent reversed ∧ ¬ Ascending reversed.trie ∧
    SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes (some [reversed])) = .ok (some [low]) ∧
    reversed.trie ≠ low.trie := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [reversed, Valid]
    · cbv
    · intro path
      simp [reversed, fromPathTrie, fromChildren, or_comm]
  · simp [reversed, Ascending]
  · change SourceEqualityPhysicalPayload.read (some [low.paths]) = .ok (some [low])
    simp only [SourceEqualityPhysicalPayload.read, recordsOf, low, lowBuilt]
    cbv
  · intro same
    have representation := Trie.branch.inj same
    have indices := congrArg (List.map Prod.fst) representation
    change [1, 0] = [0, 1] at indices
    contradiction

end MicroCFTA.PayloadReadbackKernels
