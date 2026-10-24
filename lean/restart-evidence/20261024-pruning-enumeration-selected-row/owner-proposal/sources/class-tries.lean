import MicroCFTA.EnumerationIntersection
import MicroCFTA.EqualityTermination

/-!
# Source equality readback for enumeration

Normalized classes contain at least two distinct paths. Their PCS semantics
therefore agrees with the enumerator's common-subtree semantics. The source
normalizer and checked trie constructor derive the equality conjunction and
contradiction laws used by constructor-row intersection.
-/

namespace MicroCFTA.EnumerationEquality
open Language EnumerationCorrectness EqualityNormalize

/-- Read a canonical path class through the source trie constructor. -/
def classTrie (paths : Class) : EqualityTrie.Trie :=
  (EqualityTrie.toPathTrie paths.eraseDups).getD .empty

/-- The source stores one trie for each normalized equality class. -/
def readClasses (classes : Constraints) : List EqualityTrie.Trie := classes.map classTrie

/-- Every normalized class has a valid trie with exactly its paths. -/
theorem classTrie_readback (fuel : Nat) (classes output : Constraints)
    (success : mkEqConstraints fuel classes = .normalized output) (paths : Class) (member : paths ∈ output) :
    EqualityTrie.Valid (classTrie paths) ∧ ∀ path, path ∈ EqualityTrie.fromPathTrie (classTrie paths) ↔ path ∈ paths := by
  obtain ⟨trie, built, valid, _, _, same⟩ := normalized_class_trie fuel classes output success paths member
  simpa [classTrie, built] using And.intro valid same

/-- The source's normalized trie list supplies all canonicality premises. -/
theorem readClasses_valid (fuel : Nat) (classes output : Constraints)
    (success : mkEqConstraints fuel classes = .normalized output) :
    ∀ trie ∈ readClasses output, EqualityTrie.Valid trie := by
  intro trie member
  obtain ⟨paths, present, rfl⟩ := List.mem_map.mp member
  exact (classTrie_readback fuel classes output success paths present).1

/-- Nontrivial path classes have exactly the common-subtree meaning used by enumeration. -/
theorem trie_pcs_exact (term : Term Symbol) (trie : EqualityTrie.Trie) (paths : Class)
    (same : ∀ path, path ∈ EqualityTrie.fromPathTrie trie ↔ path ∈ paths) (active : Nontrivial paths) :
    EqualityHolds term trie ↔ ClassSat term paths := by
  constructor
  · rintro ⟨common, all⟩ left leftMember right rightMember _
    exact ⟨common, all left ((same left).mpr leftMember), all right ((same right).mpr rightMember)⟩
  · intro satisfied
    obtain ⟨first, firstMember, second, secondMember, different⟩ := active
    obtain ⟨common, atFirst, _⟩ := satisfied first firstMember second secondMember different
    refine ⟨common, ?_⟩
    intro path member
    by_cases equal : path = first
    · simpa only [equal] using atFirst
    · obtain ⟨other, atPath, otherAtFirst⟩ := satisfied path ((same path).mp member) first firstMember equal
      have equalValue : other = common := Option.some.inj (otherAtFirst.symm.trans atFirst)
      simpa only [equalValue] using atPath

/-- Normalizer output tries preserve exactly the original equality constraints. -/
theorem normalized_readback_exact (term : Term Symbol) (fuel : Nat) (classes output : Constraints)
    (success : mkEqConstraints fuel classes = .normalized output) :
    (∀ trie ∈ readClasses output, EqualityHolds term trie) ↔ EqualityNormalize.Satisfies term classes := by
  have actual : (∀ trie ∈ readClasses output, EqualityHolds term trie) ↔ EqualityNormalize.Satisfies term output := by
    simp only [readClasses, List.forall_mem_map, EqualityNormalize.Satisfies]
    apply forall_congr'
    intro paths
    apply forall_congr'
    intro member
    exact trie_pcs_exact term (classTrie paths) paths
      (classTrie_readback fuel classes output success paths member).2
      ((mkEqConstraints_invariants fuel classes output success).1 paths member)
  have semantics := mkEqConstraints_correct term fuel classes (by simp [success])
  simp only [success, RunSat] at semantics
  exact actual.trans semantics

/-- Existing normalized source tries can be read back as PCS path classes. -/
theorem tries_pcs_exact (term : Term Symbol) (tries : List EqualityTrie.Trie)
    (active : ∀ trie ∈ tries, Nontrivial (EqualityTrie.fromPathTrie trie)) :
    (∀ trie ∈ tries, EqualityHolds term trie) ↔ EqualityNormalize.Satisfies term (tries.map EqualityTrie.fromPathTrie) := by
  simp only [EqualityNormalize.Satisfies, List.forall_mem_map]
  apply forall_congr'
  intro trie
  apply forall_congr'
  intro member
  exact trie_pcs_exact term trie _ (fun _ => Iff.rfl) (active trie member)

/-- The source normalized equality conjunction supplies the product guard's equality part. -/
theorem conjoin_readback_exact (term : Term Symbol) (fuel : Nat) (left right : List EqualityTrie.Trie)
    (leftActive : ∀ trie ∈ left, Nontrivial (EqualityTrie.fromPathTrie trie))
    (rightActive : ∀ trie ∈ right, Nontrivial (EqualityTrie.fromPathTrie trie))
    (output : Constraints)
    (success : mkEqConstraints fuel ((left ++ right).map EqualityTrie.fromPathTrie) = .normalized output) :
    (∀ trie ∈ readClasses output, EqualityHolds term trie) ↔
      (∀ trie ∈ left, EqualityHolds term trie) ∧ (∀ trie ∈ right, EqualityHolds term trie) := by
  rw [normalized_readback_exact term fuel _ output success,
    ← tries_pcs_exact term (left ++ right) (by
      intro trie member
      rcases List.mem_append.mp member with member | member
      · exact leftActive trie member
      · exact rightActive trie member)]
  simp only [List.mem_append, or_imp, forall_and]

/-- A contradictory normalized conjunction has no satisfying pair of source equality lists. -/
theorem conjoin_contradiction (term : Term Symbol) (fuel : Nat) (left right : List EqualityTrie.Trie)
    (leftActive : ∀ trie ∈ left, Nontrivial (EqualityTrie.fromPathTrie trie))
    (rightActive : ∀ trie ∈ right, Nontrivial (EqualityTrie.fromPathTrie trie))
    (rejected : mkEqConstraints fuel ((left ++ right).map EqualityTrie.fromPathTrie) = .contradiction) :
    ¬ ((∀ trie ∈ left, EqualityHolds term trie) ∧ (∀ trie ∈ right, EqualityHolds term trie)) := by
  intro satisfied
  have actual : ∀ trie ∈ left ++ right, EqualityHolds term trie := by simpa only [List.mem_append, or_imp, forall_and] using satisfied
  have pcs := (tries_pcs_exact term (left ++ right) (by
    intro trie member
    rcases List.mem_append.mp member with member | member
    · exact leftActive trie member
    · exact rightActive trie member)).mp actual
  have impossible := (mkEqConstraints_correct term fuel _ (by rw [rejected]; intro impossible; cases impossible)).mpr pcs
  simp only [rejected, RunSat] at impossible

/-- Normalized equalities and residual conjunction give the exact copied product guard. -/
theorem edgeView_conjoin (meaning : Guard → Term Symbol → Prop) (meet : Nat → Nat → Nat)
    (first second : EnumerationState.Edge Symbol Guard) (fuel : Nat)
    (leftActive : ∀ trie ∈ first.equalities, Nontrivial (EqualityTrie.fromPathTrie trie))
    (rightActive : ∀ trie ∈ second.equalities, Nontrivial (EqualityTrie.fromPathTrie trie))
    (output : Constraints)
    (success : mkEqConstraints fuel ((first.equalities ++ second.equalities).map EqualityTrie.fromPathTrie) = .normalized output)
    (residual : Option Guard)
    (residualCorrect : ∀ term, ResidualHolds meaning residual term ↔
      ResidualHolds meaning first.residual term ∧ ResidualHolds meaning second.residual term) :
    EnumerationLanguage.edgeView meaning
      ⟨first.symbol, (first.children.zip second.children).map (fun pair => meet pair.1 pair.2), readClasses output, residual⟩ =
      EnumerationIntersection.joinedEdge meet (EnumerationLanguage.edgeView meaning first) (EnumerationLanguage.edgeView meaning second) := by
  classical
  have guards : (fun term => decide ((∀ trie ∈ readClasses output, EqualityHolds term trie) ∧ ResidualHolds meaning residual term)) =
      (fun term => decide ((∀ trie ∈ first.equalities, EqualityHolds term trie) ∧ ResidualHolds meaning first.residual term) &&
        decide ((∀ trie ∈ second.equalities, EqualityHolds term trie) ∧ ResidualHolds meaning second.residual term)) := by
    funext term
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true, conjoin_readback_exact term fuel _ _ leftActive rightActive output success,
      residualCorrect]
    exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
  exact congrArg (fun guard => Language.Edge.mk first.symbol
    ((first.children.zip second.children).map (fun pair => meet pair.1 pair.2)) guard) guards

/-- Source equality contradiction makes the complete joined guard false, irrespective of residuals. -/
theorem edgeView_contradiction (meaning : Guard → Term Symbol → Prop) (meet : Nat → Nat → Nat)
    (first second : EnumerationState.Edge Symbol Guard) (fuel : Nat)
    (leftActive : ∀ trie ∈ first.equalities, Nontrivial (EqualityTrie.fromPathTrie trie))
    (rightActive : ∀ trie ∈ second.equalities, Nontrivial (EqualityTrie.fromPathTrie trie))
    (rejected : mkEqConstraints fuel ((first.equalities ++ second.equalities).map EqualityTrie.fromPathTrie) = .contradiction)
    (term : Term Symbol) :
    (EnumerationIntersection.joinedEdge meet (EnumerationLanguage.edgeView meaning first)
      (EnumerationLanguage.edgeView meaning second)).guard term = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro accepted
  have inputs : ((∀ trie ∈ first.equalities, EqualityHolds term trie) ∧ ResidualHolds meaning first.residual term) ∧
      ((∀ trie ∈ second.equalities, EqualityHolds term trie) ∧ ResidualHolds meaning second.residual term) := by
    simpa only [EnumerationIntersection.joinedEdge, EnumerationLanguage.edgeView, Bool.and_eq_true, decide_eq_true_eq] using accepted
  exact conjoin_contradiction term fuel _ _ leftActive rightActive rejected ⟨inputs.1.1, inputs.2.1⟩

end MicroCFTA.EnumerationEquality
