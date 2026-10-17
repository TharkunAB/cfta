import MicroCFTA.SourceCurrentEqualityDependencyDescent

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.DependencyDescentKernels
open EqualityNormalize SourceEqualityClassOrder SourceEqualityDescend
open SourceCurrentEqualityNormalizationFixed SourceCurrentEqualityDependencyDescent

private def basePaths : Class := [[0, 0], [0, 1], [1]]
private def dependentPaths : Class := [[0, 0, 0], [0, 1, 0], [1, 0]]
private def rawPaths : Class := [[0, 2], [0, 3], [1, 0]]
private def physical (paths : Class) : Record :=
  (recordOf paths).getD ⟨.empty, []⟩
private def first := physical basePaths
private def second := physical dependentPaths
private def raw := physical rawPaths
private def child (value : Record) := fromTrie (EqualityTrie.pathTrieDescend value.trie 0)

private theorem constructed_record (paths : Class) (value : Record) (built : recordOf paths = some value) :
    Coherent value ∧ EqualityTrie.Ascending value.trie := by
  cases source : EqualityTrie.toPathTrie paths.eraseDups with
  | none => simp [recordOf, source] at built
  | some trie =>
      have supported := EqualityTrie.build_requires_supported (EqualityTrie.pathBudget paths.eraseDups)
        paths.eraseDups trie source
      obtain ⟨actual, done, coherent, _⟩ := recordOf_complete paths supported
      have same := Option.some.inj (done.symm.trans built)
      subst actual
      exact ⟨coherent, recordOf_ascending paths value built⟩

private theorem firstFacts : Coherent first ∧ EqualityTrie.Ascending first.trie ∧ Nontrivial first.paths := by
  have built : recordOf basePaths = some first := by cbv
  have known := constructed_record basePaths first built
  exact ⟨known.1, known.2, [0, 0], by cbv; exact List.Mem.head _, [0, 1], by cbv; exact List.Mem.tail _ (List.Mem.head _), by decide⟩

private theorem secondFacts : Coherent second ∧ EqualityTrie.Ascending second.trie ∧ Nontrivial second.paths := by
  have built : recordOf dependentPaths = some second := by cbv
  have known := constructed_record dependentPaths second built
  exact ⟨known.1, known.2, [0, 0, 0], by cbv; exact List.Mem.head _, [0, 1, 0], by cbv; exact List.Mem.tail _ (List.Mem.head _), by decide⟩

private theorem rawFacts : Coherent raw ∧ EqualityTrie.Ascending raw.trie ∧ Nontrivial raw.paths := by
  have built : recordOf rawPaths = some raw := by cbv
  have known := constructed_record rawPaths raw built
  exact ⟨known.1, known.2, [0, 2], by cbv; exact List.Mem.head _, [0, 3], by cbv; exact List.Mem.tail _ (List.Mem.head _), by decide⟩

private theorem pair_wellFormed (left right : Record)
    (firstKnown : Coherent left ∧ EqualityTrie.Ascending left.trie ∧ Nontrivial left.paths)
    (secondKnown : Coherent right ∧ EqualityTrie.Ascending right.trie ∧ Nontrivial right.paths) :
    WellFormed (some [left, right]) := by
  intro originals same value member
  cases same
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact firstKnown
  · exact secondKnown

/-- A dependency witnessed outside child zero produces a nontrivial actual dependent child there. -/
theorem saturated_retention :
    SourceEqualityPhysicalPayload.read (some [basePaths, dependentPaths]) = .ok (some [first, second]) ∧
    WellFormed (some [first, second]) ∧ Fixed ([first, second].map Record.paths) ∧
    [1] ∈ first.paths ∧ [1, 0] ∈ second.paths ∧
    ∃ output, record 0 first = some (child first) ∧ record 0 second = some output ∧
      output ∈ records 0 [first, second] ∧ Subsumes (child first).paths output.paths ∧
      [0] ∈ (child first).paths ∧ [0, 0] ∈ output.paths := by
  have wellFormed := pair_wellFormed first second firstFacts secondFacts
  have fixed : Fixed ([first, second].map Record.paths) := by
    have fields : [first, second].map Record.paths = [basePaths, dependentPaths] := by cbv
    rw [fields]
    apply of_step _
    · intro paths member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨[0, 0], by cbv; exact List.Mem.head _, [0, 1], by cbv; exact List.Mem.tail _ (List.Mem.head _), by decide⟩
      · exact ⟨[0, 0, 0], by cbv; exact List.Mem.head _, [0, 1, 0], by cbv; exact List.Mem.tail _ (List.Mem.head _), by decide⟩
    · cbv
  have initial : Subsumes first.paths second.paths :=
    ⟨[1], by cbv; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), [1, 0], by cbv; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), ⟨[0], rfl⟩, by decide⟩
  have called : record 0 first = some (child first) := by cbv
  obtain ⟨output, built, included, dependency⟩ := retained [first, second] wellFormed fixed 0 first second
    (by simp) (by simp) initial (child first) called
  have expected : record 0 second = some (child second) := by cbv
  have same := Option.some.inj (built.symm.trans expected)
  subst output
  exact ⟨by cbv, wellFormed, fixed, by cbv; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), by cbv; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), child second, called, built, included,
    dependency, by cbv; exact List.Mem.head _, by cbv; exact List.Mem.head _⟩

/-- Coherent consistent records without saturation can lose a parent dependency at the selected child. -/
theorem saturation_boundary :
    WellFormed (some [first, raw]) ∧ isContradicting ([first, raw].map Record.paths) = false ∧
    Subsumes first.paths raw.paths ∧
    record 0 first = some (child first) ∧ record 0 raw = some (child raw) ∧
    ¬ Subsumes (child first).paths (child raw).paths ∧ ¬ Fixed ([first, raw].map Record.paths) := by
  have wellFormed := pair_wellFormed first raw firstFacts rawFacts
  have initial : Subsumes first.paths raw.paths :=
    ⟨[1], by cbv; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), [1, 0], by cbv; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), ⟨[0], rfl⟩, by decide⟩
  have called : record 0 first = some (child first) := by cbv
  have other : record 0 raw = some (child raw) := by cbv
  have absent : ¬ Subsumes (child first).paths (child raw).paths := by
    have fields : (child first).paths = [[0], [1]] ∧ (child raw).paths = [[2], [3]] := by cbv
    rw [fields.1, fields.2]
    simp [Subsumes]
  refine ⟨wellFormed, by cbv, initial, called, other, absent, ?_⟩
  intro fixed
  exact absent ((subsumes_iff [first, raw] wellFormed fixed 0 first raw (by simp) (by simp)
    (child first) (child raw) called other).mpr initial)

end MicroCFTA.DependencyDescentKernels
