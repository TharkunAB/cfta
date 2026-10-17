import MicroCFTA.SourceCurrentEqualityNormalizationFixed
import MicroCFTA.SourceEqualityInheritedPayload
import MicroCFTA.SourceListSortOrdered

/-!
# Saturation of actual inherited trie descent

Actual descent restricts each parent class to one child. Every generated
suffix equality remains in a descended parent component. The source sorter
retains the literal canonical order of those components.
-/
namespace MicroCFTA.SourceCurrentEqualityDescendFixed
open EqualityNormalize SourceEqualityClassOrder SourceEqualityDescend
open SourceCurrentEqualityNormalizationFixed

private theorem member_origin (index : Nat) (originals : List Record) (output : Record)
    (member : output ∈ records index originals) :
    ∃ original ∈ originals, record index original = some output :=
  List.mem_filterMap.mp ((records_perm index originals).mem_iff.mp member)

private theorem record_retained (index : Nat) (original : Record) (coherent : Coherent original)
    (left right : List Nat) (leftMember : index :: left ∈ original.paths)
    (rightMember : index :: right ∈ original.paths) (different : left ≠ right) :
    ∃ output, record index original = some output := by
  have valid := EqualityTrie.descend_valid original.trie coherent.1 index
  have pairs := EqualityTrie.descend_exact original.trie coherent.1 index
  have kept := (EqualitySaturation.pathTrieHasAtLeastTwoPaths_nontrivial _ valid).mpr
    ⟨left, (pairs left).mpr ((coherent.2.2 _).mpr leftMember),
      right, (pairs right).mpr ((coherent.2.2 _).mpr rightMember), different⟩
  exact ⟨fromTrie (EqualityTrie.pathTrieDescend original.trie index), by simp only [record, kept, ite_true]⟩

/-- Every actual descended class remains active and canonical. -/
theorem records_invariants (originals : List Record) (wellFormed : WellFormed (some originals)) (index : Nat) :
    Active ((records index originals).map Record.paths) ∧
      ∀ paths ∈ (records index originals).map Record.paths, canonicalClass paths = paths := by
  have facts (output : Record) (member : output ∈ records index originals) :
      Coherent output ∧ EqualityTrie.Ascending output.trie ∧ Nontrivial output.paths := by
    obtain ⟨original, originalMember, found⟩ := member_origin index originals output member
    have known := wellFormed originals rfl original originalMember
    exact record_wellFormed index original known.1 known.2.1 output found
  constructor
  · intro paths member
    obtain ⟨output, included, rfl⟩ := List.mem_map.mp member
    exact (facts output included).2.2
  · intro paths member
    obtain ⟨output, included, rfl⟩ := List.mem_map.mp member
    exact (facts output included).1.2.1

/-- Actual child classes retain the parent's disjoint component partition. -/
theorem records_disjoint (originals : List Record) (wellFormed : WellFormed (some originals))
    (disjoint : (originals.map Record.paths).Pairwise (fun left right => overlap left right = false))
    (index : Nat) :
    ((records index originals).map Record.paths).Pairwise (fun left right => overlap left right = false) := by
  apply List.pairwise_map.mpr
  apply ((records_perm index originals).symm.pairwise_iff (by
    intro first second known
    simpa only [overlap_symm second.paths first.paths] using known)).mp
  apply List.pairwise_filterMap.mpr
  apply (List.pairwise_map.mp disjoint).imp_of_mem
  intro first second firstMember secondMember separate left leftFound right rightFound
  apply Bool.eq_false_iff.mpr
  intro shared
  obtain ⟨path, inLeft, inRight⟩ := (overlap_correct _ _).mp shared
  have firstPair := record_pairs index first (wellFormed originals rfl first firstMember).1 left leftFound
  have secondPair := record_pairs index second (wellFormed originals rfl second secondMember).1 right rightFound
  have parentShared := (overlap_correct _ _).mpr
    ⟨index :: path, (firstPair path).mp inLeft, (secondPair path).mp inRight⟩
  rw [separate] at parentShared
  contradiction

/-- A consistent parent cannot acquire a strict-prefix contradiction through actual trie descent. -/
theorem records_consistent (originals : List Record) (wellFormed : WellFormed (some originals))
    (consistent : isContradicting (originals.map Record.paths) = false) (index : Nat) :
    isContradicting ((records index originals).map Record.paths) = false := by
  apply Bool.eq_false_iff.mpr
  intro contradiction
  obtain ⟨paths, member, left, leftMember, right, rightMember, initial, different⟩ :=
    (isContradicting_correct _).mp contradiction
  obtain ⟨output, included, rfl⟩ := List.mem_map.mp member
  obtain ⟨original, originalMember, found⟩ := member_origin index originals output included
  have pairs := record_pairs index original (wellFormed originals rfl original originalMember).1 output found
  obtain ⟨suffix, equal⟩ := initial
  have parentContra := (isContradicting_correct _).mpr
    ⟨original.paths, List.mem_map.mpr ⟨original, originalMember, rfl⟩,
      index :: left, (pairs left).mp leftMember, index :: right, (pairs right).mp rightMember,
      ⟨suffix, by simpa only [List.cons_append] using congrArg (index :: ·) equal⟩,
      by simpa only [ne_eq, List.cons.injEq, true_and] using different⟩
  rw [consistent] at parentContra
  contradiction

/-- Every suffix congruence generated after actual descent lies in an existing descended component. -/
theorem records_closed (originals : List Record) (wellFormed : WellFormed (some originals))
    (fixed : congruenceStep (originals.map Record.paths) = some (originals.map Record.paths)) (index : Nat) :
    Covers (addCongruences ((records index originals).map Record.paths))
      ((records index originals).map Record.paths) := by
  intro paths member
  rcases List.mem_append.mp member with original | generated
  · exact ⟨paths, original, fun _ present => present⟩
  obtain ⟨source, sourceMember, generated⟩ := List.mem_flatMap.mp generated
  obtain ⟨suffix, suffixMember, rfl⟩ := List.mem_map.mp generated
  obtain ⟨output, outputMember, rfl⟩ := List.mem_map.mp sourceMember
  obtain ⟨parent, parentMember, parentFound⟩ := member_origin index originals output outputMember
  have parentKnown := wellFormed originals rfl parent parentMember
  have parentPairs := record_pairs index parent parentKnown.1 output parentFound
  obtain ⟨base, baseMember, extension, extensionMember, nonempty, equal⟩ :=
    (mem_suffixes _ _ _).mp suffixMember
  obtain ⟨extensionClass, extensionClassMember, extensionMember⟩ := (mem_members _ _).mp extensionMember
  obtain ⟨extensionOutput, extensionOutputMember, rfl⟩ := List.mem_map.mp extensionClassMember
  obtain ⟨extensionParent, extensionParentMember, extensionFound⟩ :=
    member_origin index originals extensionOutput extensionOutputMember
  have extensionPairs := record_pairs index extensionParent
    (wellFormed originals rfl extensionParent extensionParentMember).1 extensionOutput extensionFound
  have requested : suffix ∈ suffixes parent.paths (originals.map Record.paths) :=
    (mem_suffixes _ _ _).mpr ⟨index :: base, (parentPairs base).mp baseMember,
      index :: extension, (mem_members _ _).mpr
        ⟨extensionParent.paths, List.mem_map.mpr ⟨extensionParent, extensionParentMember, rfl⟩,
          (extensionPairs extension).mp extensionMember⟩,
      nonempty, by simpa only [List.cons_append] using congrArg (index :: ·) equal⟩
  obtain ⟨component, componentMember, includes⟩ := fixedPoint_congruence_closed
    (originals.map Record.paths) fixed parent.paths (List.mem_map.mpr ⟨parent, parentMember, rfl⟩) suffix requested
  obtain ⟨componentRecord, componentRecordMember, rfl⟩ := List.mem_map.mp componentMember
  obtain ⟨left, leftMember, right, rightMember, different⟩ :=
    (record_wellFormed index parent parentKnown.1 parentKnown.2.1 output parentFound).2.2
  have leftExtended : index :: (left ++ suffix) ∈ componentRecord.paths := by
    simpa only [List.cons_append] using includes (index :: left) ((parentPairs left).mp leftMember)
  have rightExtended : index :: (right ++ suffix) ∈ componentRecord.paths := by
    simpa only [List.cons_append] using includes (index :: right) ((parentPairs right).mp rightMember)
  obtain ⟨descended, descendedFound⟩ := record_retained index componentRecord
    (wellFormed originals rfl componentRecord componentRecordMember).1
    (left ++ suffix) (right ++ suffix) leftExtended rightExtended
    (fun same => different (List.append_cancel_right same))
  have descendedMember : descended ∈ records index originals :=
    (records_perm index originals).mem_iff.mpr
      (List.mem_filterMap.mpr ⟨componentRecord, componentRecordMember, descendedFound⟩)
  have descendedPairs := record_pairs index componentRecord
    (wellFormed originals rfl componentRecord componentRecordMember).1 descended descendedFound
  refine ⟨descended.paths, List.mem_map.mpr ⟨descended, descendedMember, rfl⟩, ?_⟩
  intro path present
  obtain ⟨base, baseMember, rfl⟩ := (mem_extendClass _ _ _).mp present
  apply (descendedPairs _).mpr
  simpa only [List.cons_append] using includes (index :: base) ((parentPairs base).mp baseMember)

private theorem complete_of_closed (classes : Constraints) (normal : EqualitySaturation.NormalState classes)
    (closed : Covers (addCongruences classes) classes) : complete (addCongruences classes) = classes := by
  apply complete_matches_partition _ classes (addCongruences_active classes normal.1)
    normal.1 normal.2.1 normal.2.2.1 normal.2.2.2
  intro left right
  constructor
  · rintro ⟨paths, member, first, second⟩
    exact .edge paths (List.mem_append_left _ member) first second
  · intro connected
    induction connected with
    | edge paths member first second =>
        obtain ⟨component, included, contains⟩ := closed paths member
        exact ⟨component, included, contains _ first, contains _ second⟩
    | @trans left middle right _ _ firstIH secondIH =>
        obtain ⟨first, firstMember, leftMember, firstPivot⟩ := firstIH
        obtain ⟨second, secondMember, secondPivot, rightMember⟩ := secondIH
        have same := components_equal classes normal.2.1 first second firstMember secondMember
          middle firstPivot secondPivot
        subst second
        exact ⟨first, firstMember, leftMember, rightMember⟩

private theorem records_step_of_ordered (originals : List Record) (wellFormed : WellFormed (some originals))
    (fixed : Fixed (originals.map Record.paths)) (index : Nat)
    (ordered : ((records index originals).map Record.paths).Pairwise (· ≤ ·)) :
    congruenceStep ((records index originals).map Record.paths) =
      some ((records index originals).map Record.paths) := by
  have known := invariants _ fixed
  have child := records_invariants originals wellFormed index
  have normal : EqualitySaturation.NormalState ((records index originals).map Record.paths) :=
    ⟨child.1, records_disjoint originals wellFormed known.2.2.1 index, ordered, child.2⟩
  have completed := complete_of_closed _ normal (records_closed originals wellFormed known.2.2.2 index)
  have consistent := records_consistent originals wellFormed known.2.1 index
  simp only [congruenceStep, completed, consistent, Bool.false_eq_true, ite_false]

/-- The actual source sorter orders all retained child classes by their path sets. -/
theorem records_ordered (originals : List Record) (index : Nat) :
    ((records index originals).map Record.paths).Pairwise (· ≤ ·) := by
  dsimp only [records]
  split
  · simp
  · simp
  · exact List.pairwise_map.mpr (SourceListSortOrdered.paths _)

/-- One executable congruence step retains the literal actual descended class list. -/
theorem records_step (originals : List Record) (wellFormed : WellFormed (some originals))
    (fixed : Fixed (originals.map Record.paths)) (index : Nat) :
    congruenceStep ((records index originals).map Record.paths) =
      some ((records index originals).map Record.paths) :=
  records_step_of_ordered originals wellFormed fixed index (records_ordered originals index)

/-- Actual trie descent preserves exact source normalization fixedness. -/
theorem records_fixed (originals : List Record) (wellFormed : WellFormed (some originals))
    (fixed : Fixed (originals.map Record.paths)) (index : Nat) :
    Fixed ((records index originals).map Record.paths) :=
  of_step _ (records_invariants originals wellFormed index).1 (records_step originals wellFormed fixed index)

/-- Every actual successful child payload inherits the initial source normalization fixed point. -/
theorem descend_fixed (input : SourceEqualityPrecheck.Constraint) (wellFormed : WellFormed input)
    (fixed : ∀ originals, input = some originals → Fixed (originals.map Record.paths)) (index : Nat) :
    ∀ outputs, descend input index = some outputs → Fixed (outputs.map Record.paths) := by
  cases input with
  | none => intro outputs impossible; cases impossible
  | some originals =>
      intro outputs actual
      have same : records index originals = outputs := by
        cases originals <;> exact Option.some.inj actual
      rw [← same]
      exact records_fixed originals wellFormed (fixed originals rfl) index

end MicroCFTA.SourceCurrentEqualityDescendFixed
