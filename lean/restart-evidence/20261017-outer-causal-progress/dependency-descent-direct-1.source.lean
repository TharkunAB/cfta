import MicroCFTA.SourceCurrentEqualityDescendFixed

/-!
# Exact class dependencies through actual inherited descent

Saturation extends every path of a class by the same dependency suffix.
If that class survives a selected child descent, every dependent class
also survives. Their strict-prefix dependency remains exact.
This is a local payload result. It does not rank outer source occurrences.
-/
namespace MicroCFTA.SourceCurrentEqualityDependencyDescent
open EqualityNormalize SourceEqualityClassOrder SourceEqualityDescend
open SourceCurrentEqualityNormalizationFixed

private theorem uniform_suffix (classes : Constraints)
    (fixed : congruenceStep classes = some classes) (first second : Class)
    (firstMember : first ∈ classes) (secondMember : second ∈ classes)
    (dependent : Subsumes first second) :
    ∃ suffix, suffix ≠ [] ∧ ∀ path ∈ first, path ++ suffix ∈ second := by
  obtain ⟨base, baseMember, extended, extendedMember, ⟨suffix, equal⟩, different⟩ := dependent
  have nonempty : suffix ≠ [] := by
    intro empty
    simp only [empty, List.append_nil] at equal
    exact different equal
  have requested : suffix ∈ suffixes first classes :=
    (mem_suffixes first classes suffix).mpr
      ⟨base, baseMember, extended, (mem_members classes extended).mpr
        ⟨second, secondMember, extendedMember⟩, nonempty, equal⟩
  obtain ⟨component, member, includes⟩ :=
    fixedPoint_congruence_closed classes fixed first firstMember suffix requested
  have common : extended ∈ component := equal ▸ includes base baseMember
  have same := components_equal classes (congruenceStep_disjoint classes classes fixed)
    component second member secondMember extended common extendedMember
  subst component
  exact ⟨suffix, nonempty, includes⟩

/-- Retaining a source class produces a retained dependent class at the same actual child. -/
theorem retained (originals : List Record) (wellFormed : WellFormed (some originals))
    (fixed : Fixed (originals.map Record.paths)) (index : Nat) (first second : Record)
    (firstMember : first ∈ originals) (secondMember : second ∈ originals)
    (dependent : Subsumes first.paths second.paths) (firstOutput : Record)
    (firstRead : record index first = some firstOutput) :
    ∃ secondOutput, record index second = some secondOutput ∧
      secondOutput ∈ records index originals ∧ Subsumes firstOutput.paths secondOutput.paths := by
  have firstKnown := wellFormed originals rfl first firstMember
  have secondKnown := wellFormed originals rfl second secondMember
  obtain ⟨suffix, nonempty, includes⟩ := uniform_suffix (originals.map Record.paths)
    (invariants _ fixed).2.2.2 first.paths second.paths
    (List.mem_map.mpr ⟨first, firstMember, rfl⟩) (List.mem_map.mpr ⟨second, secondMember, rfl⟩) dependent
  have firstPairs := record_pairs index first firstKnown.1 firstOutput firstRead
  obtain ⟨left, leftMember, right, rightMember, different⟩ :=
    (record_wellFormed index first firstKnown.1 firstKnown.2.1 firstOutput firstRead).2.2
  have firstExtended : index :: (left ++ suffix) ∈ second.paths := by
    simpa only [List.cons_append] using includes (index :: left) ((firstPairs left).mp leftMember)
  have secondExtended : index :: (right ++ suffix) ∈ second.paths := by
    simpa only [List.cons_append] using includes (index :: right) ((firstPairs right).mp rightMember)
  have valid := EqualityTrie.descend_valid second.trie secondKnown.1.1 index
  have pairs := EqualityTrie.descend_exact second.trie secondKnown.1.1 index
  have kept := (EqualitySaturation.pathTrieHasAtLeastTwoPaths_nontrivial _ valid).mpr
    ⟨left ++ suffix, (pairs _).mpr ((secondKnown.1.2.2 _).mpr firstExtended),
      right ++ suffix, (pairs _).mpr ((secondKnown.1.2.2 _).mpr secondExtended),
      fun same => different (List.append_cancel_right same)⟩
  let output := fromTrie (EqualityTrie.pathTrieDescend second.trie index)
  have built : record index second = some output := by simp only [record, kept, ite_true]; rfl
  have outputPairs := record_pairs index second secondKnown.1 output built
  refine ⟨output, built, (records_perm index originals).mem_iff.mpr
    (List.mem_filterMap.mpr ⟨second, secondMember, built⟩), left, leftMember,
    left ++ suffix, (outputPairs _).mpr firstExtended, ⟨suffix, rfl⟩, ?_⟩
  intro same
  have lengths := congrArg List.length same
  have positive := List.length_pos_iff.mpr nonempty
  simp only [List.length_append] at lengths
  omega

/-- Actual retained child records have exactly their original strict-prefix dependency. -/
theorem subsumes_iff (originals : List Record) (wellFormed : WellFormed (some originals))
    (fixed : Fixed (originals.map Record.paths)) (index : Nat) (first second : Record)
    (firstMember : first ∈ originals) (secondMember : second ∈ originals)
    (firstOutput secondOutput : Record) (firstRead : record index first = some firstOutput)
    (secondRead : record index second = some secondOutput) :
    Subsumes firstOutput.paths secondOutput.paths ↔ Subsumes first.paths second.paths := by
  constructor
  · rintro ⟨left, leftMember, right, rightMember, ⟨suffix, equal⟩, different⟩
    have firstPairs := record_pairs index first (wellFormed originals rfl first firstMember).1 firstOutput firstRead
    have secondPairs := record_pairs index second (wellFormed originals rfl second secondMember).1 secondOutput secondRead
    exact ⟨index :: left, (firstPairs left).mp leftMember, index :: right, (secondPairs right).mp rightMember,
      ⟨suffix, by simpa only [List.cons_append] using congrArg (index :: ·) equal⟩,
      by simpa only [ne_eq, List.cons.injEq, true_and] using different⟩
  · intro dependent
    obtain ⟨actual, built, _, dependency⟩ := retained originals wellFormed fixed index first second
      firstMember secondMember dependent firstOutput firstRead
    have same := Option.some.inj (built.symm.trans secondRead)
    subst actual
    exact dependency

end MicroCFTA.SourceCurrentEqualityDependencyDescent
