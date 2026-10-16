import MicroCFTA.SourceEqualityNativeDemandOpenMeaning
import MicroCFTA.SourceRecursiveIntersectionGuardedInput

/-!
# One-sided contexts for checked recursive pair references

Original languages and derivation ranks are fixed before output binders are
interpreted. Soundness tests a new binder at the original pair language.
Completeness uses a bound on the sum of two original derivation ranks.
The local containment premise in `complete_extend` is a context lemma.
A full Mu proof must derive it by smaller input ranks. This module does
not prove recursive checked meaning or validity of warm open memo entries.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePairContexts
open Language BinderLanguage InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts

variable {Symbol : Type}

/-- The common language of two independently interpreted original identities. -/
def PairLanguage (languages : Nat → Lang Symbol) (key : Nat × Nat) : Lang Symbol :=
  fun term => languages key.1 term ∧ languages key.2 term

/-- Two original derivations fit within the bound on their combined ranks. -/
def RankedPair (ranks : Nat → Nat → Lang Symbol) (bound : Nat) (key : Nat × Nat) : Lang Symbol :=
  fun term => ∃ first second, first + second ≤ bound ∧ ranks key.1 first term ∧ ranks key.2 second term

/-- Every enclosing pair reference accepts only original common terms. -/
def SoundPairs (languages : Nat → Lang Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (output : InternedGuardedLanguage.Env Symbol) : Prop :=
  ∀ key ∈ domain.seen, Included (output (.intersection key.1 key.2)) (PairLanguage languages key)

/-- Every enclosing pair reference accepts all common terms within the rank bound. -/
def CompletePairs (ranks : Nat → Nat → Lang Symbol) (bound : Nat)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol) : Prop :=
  ∀ key ∈ domain.seen, Included (RankedPair ranks bound key) (output (.intersection key.1 key.2))

/-- An empty seen set imposes no soundness obligation. -/
theorem sound_empty (languages : Nat → Lang Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (output : InternedGuardedLanguage.Env Symbol) (empty : domain.seen = []) : SoundPairs languages domain output := by
  intro key member
  simp only [empty, List.not_mem_nil] at member

/-- An empty seen set imposes no completeness obligation at any rank bound. -/
theorem complete_empty (ranks : Nat → Nat → Lang Symbol) (bound : Nat)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol)
    (empty : domain.seen = []) : CompletePairs ranks bound domain output := by
  intro key member
  simp only [empty, List.not_mem_nil] at member

/-- The actual empty source domain supplies soundness for every output environment. -/
theorem sound_empty_domain (languages : Nat → Lang Symbol) (output : InternedGuardedLanguage.Env Symbol) :
    SoundPairs languages IntersectionEmptyDomain.emptyKey output := sound_empty languages _ output rfl

/-- The actual empty source domain supplies completeness at every rank bound. -/
theorem complete_empty_domain (ranks : Nat → Nat → Lang Symbol) (bound : Nat)
    (output : InternedGuardedLanguage.Env Symbol) : CompletePairs ranks bound IntersectionEmptyDomain.emptyKey output :=
  complete_empty ranks bound _ output rfl

/-- Removing seen pairs preserves the remaining soundness obligations. -/
theorem sound_restrict (languages : Nat → Lang Symbol) (before after : IntersectionFlatMemoKeyDomain.DomainKey)
    (output : InternedGuardedLanguage.Env Symbol) (subset : ∀ key ∈ before.seen, key ∈ after.seen)
    (sound : SoundPairs languages after output) : SoundPairs languages before output :=
  fun key member => sound key (subset key member)

/-- Removing seen pairs preserves the remaining completeness obligations. -/
theorem complete_restrict (ranks : Nat → Nat → Lang Symbol) (bound : Nat)
    (before after : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol)
    (subset : ∀ key ∈ before.seen, key ∈ after.seen) (complete : CompletePairs ranks bound after output) :
    CompletePairs ranks bound before output := fun key member => complete key (subset key member)

/-- Increasing the combined bound retains both original derivations. -/
theorem ranked_pair_mono (ranks : Nat → Nat → Lang Symbol) (before after : Nat) (bounded : before ≤ after)
    (key : Nat × Nat) : Included (RankedPair ranks before key) (RankedPair ranks after key) := by
  rintro term ⟨first, second, smaller, left, right⟩
  exact ⟨first, second, Nat.le_trans smaller bounded, left, right⟩

/-- Completeness at a larger bound implies completeness at every smaller bound. -/
theorem complete_mono (ranks : Nat → Nat → Lang Symbol) (before after : Nat) (bounded : before ≤ after)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol)
    (complete : CompletePairs ranks after domain output) : CompletePairs ranks before domain output :=
  fun key member term accepted => complete key member term (ranked_pair_mono ranks before after bounded key term accepted)

private theorem intersection_ne (domain : IntersectionFlatMemoKeyDomain.DomainKey) (key other : Nat × Nat)
    (fresh : key ∉ domain.seen) (old : other ∈ domain.seen) :
    Reference.intersection other.1 other.2 ≠ .intersection key.1 key.2 := by
  intro same
  obtain ⟨first, second⟩ := Reference.intersection.inj same
  have equal : other = key := Prod.ext first second
  exact fresh (equal ▸ old)

/-- A fresh candidate that accepts only original common terms preserves soundness. -/
theorem sound_extend_candidate (languages : Nat → Lang Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (output : InternedGuardedLanguage.Env Symbol) (sound : SoundPairs languages domain output)
    (bindings : List Nat) (key : Nat × Nat) (fresh : key ∉ domain.seen) (candidate : Lang Symbol)
    (contained : Included candidate (PairLanguage languages key)) :
    SoundPairs languages (SourceRecursiveIntersectionDomain.extend domain bindings key)
      (InternedGuardedLanguage.bind output (.intersection key.1 key.2) candidate) := by
  intro other member term accepted
  rcases (SourceRecursiveIntersectionDomain.extend_seen domain bindings key other).mp member with rfl | old
  · exact contained term (by simpa only [InternedGuardedLanguage.bind, ite_true] using accepted)
  · exact sound other old term (by
      simpa only [InternedGuardedLanguage.bind, intersection_ne domain key other fresh old, ite_false] using accepted)

/-- Soundness can test a fresh binder at the fixed original pair language. -/
theorem sound_extend (languages : Nat → Lang Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (output : InternedGuardedLanguage.Env Symbol) (sound : SoundPairs languages domain output)
    (bindings : List Nat) (key : Nat × Nat) (fresh : key ∉ domain.seen) :
    SoundPairs languages (SourceRecursiveIntersectionDomain.extend domain bindings key)
      (InternedGuardedLanguage.bind output (.intersection key.1 key.2) (PairLanguage languages key)) :=
  sound_extend_candidate languages domain output sound bindings key fresh _ (fun _ accepted => accepted)

/-- A candidate containing the bounded original pair preserves completeness.
The full Mu argument must derive `contains` by smaller original input ranks. -/
theorem complete_extend (ranks : Nat → Nat → Lang Symbol) (bound : Nat)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol)
    (complete : CompletePairs ranks bound domain output) (bindings : List Nat) (key : Nat × Nat)
    (fresh : key ∉ domain.seen) (candidate : Lang Symbol)
    (contains : Included (RankedPair ranks bound key) candidate) :
    CompletePairs ranks bound (SourceRecursiveIntersectionDomain.extend domain bindings key)
      (InternedGuardedLanguage.bind output (.intersection key.1 key.2) candidate) := by
  intro other member term accepted
  rcases (SourceRecursiveIntersectionDomain.extend_seen domain bindings key other).mp member with rfl | old
  · simpa only [InternedGuardedLanguage.bind, ite_true] using contains term accepted
  · simpa only [InternedGuardedLanguage.bind, intersection_ne domain key other fresh old, ite_false]
      using complete other old term accepted

/-- The literal repeated pair reference inherits the enclosing soundness law. -/
theorem repeated_reference_sound (holds : Guard → Term Symbol → Bool) (languages : Nat → Lang Symbol)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol)
    (sound : SoundPairs languages domain output) (key : Nat × Nat) (member : key ∈ domain.seen) :
    Included (InternedGuardedLanguage.meaning holds output
      (SourceRecursiveIntersectionControl.repeatedValue key)) (PairLanguage languages key) := by
  simpa only [SourceRecursiveIntersectionControl.repeatedValue, InternedGuardedLanguage.meaning] using sound key member

/-- The literal repeated pair reference inherits bounded completeness. -/
theorem repeated_reference_complete (holds : Guard → Term Symbol → Bool) (ranks : Nat → Nat → Lang Symbol)
    (bound : Nat) (domain : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol)
    (complete : CompletePairs ranks bound domain output) (key : Nat × Nat) (member : key ∈ domain.seen) :
    Included (RankedPair ranks bound key) (InternedGuardedLanguage.meaning holds output
      (SourceRecursiveIntersectionControl.repeatedValue key)) := by
  simpa only [SourceRecursiveIntersectionControl.repeatedValue, InternedGuardedLanguage.meaning] using complete key member

/-- Erasing the sum bound recovers the intersection of the two ranked input languages. -/
theorem ranked_pair_exact (languages : Nat → Lang Symbol) (ranks : Nat → Nat → Lang Symbol)
    (exactRanks : ∀ name term, languages name term ↔ ∃ rank, ranks name rank term)
    (key : Nat × Nat) (term : Term Symbol) :
    PairLanguage languages key term ↔ ∃ bound, RankedPair ranks bound key term := by
  constructor
  · rintro ⟨left, right⟩
    obtain ⟨first, left⟩ := (exactRanks key.1 term).mp left
    obtain ⟨second, right⟩ := (exactRanks key.2 term).mp right
    exact ⟨first + second, first, second, Nat.le_refl _, left, right⟩
  · rintro ⟨_, first, second, _, left, right⟩
    exact ⟨(exactRanks key.1 term).mpr ⟨first, left⟩, (exactRanks key.2 term).mpr ⟨second, right⟩⟩

/-- Soundness and completeness at all ranks give exact repeated-reference meaning. -/
theorem repeated_reference_exact (holds : Guard → Term Symbol → Bool) (languages : Nat → Lang Symbol)
    (ranks : Nat → Nat → Lang Symbol)
    (exactRanks : ∀ name term, languages name term ↔ ∃ rank, ranks name rank term)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (output : InternedGuardedLanguage.Env Symbol)
    (sound : SoundPairs languages domain output) (complete : ∀ bound, CompletePairs ranks bound domain output)
    (key : Nat × Nat) (member : key ∈ domain.seen) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds output (SourceRecursiveIntersectionControl.repeatedValue key) term ↔
      PairLanguage languages key term := by
  constructor
  · exact repeated_reference_sound holds languages domain output sound key member term
  · intro accepted
    obtain ⟨bound, bounded⟩ := (ranked_pair_exact languages ranks exactRanks key term).mp accepted
    exact repeated_reference_complete holds ranks bound domain output (complete bound) key member term bounded

/-- Independent finite input derivations provide the exact rank-erasure law. -/
theorem finite_ranks_exact (view : IntersectSchedule.View Symbol) (inputs : IntersectSchedule.FiniteInput view)
    (name : Nat) (term : Term Symbol) :
    IntersectSchedule.finiteLanguages view inputs name term ↔
      ∃ rank, IntersectSchedule.finiteRanks view inputs name rank term := Iff.rfl

/-- Actual closed original roots derive fixed input models and their physical languages.
These models describe only the original inputs. They do not assert a checked result law. -/
theorem source_input_models (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (left right : Value Symbol Guard)
    (leftOriginal : SourceRecursiveIntersectionInputView.Original left)
    (rightOriginal : SourceRecursiveIntersectionInputView.Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ (model : IntersectSchedule.InputMeaning (SourceRecursiveIntersectionInputView.view source holds))
      (ranked : IntersectSchedule.RankedInput (SourceRecursiveIntersectionInputView.view source holds) model.valid),
      model.valid (SourceRecursiveIntersectionInputView.inputOf left) ∧
      model.valid (SourceRecursiveIntersectionInputView.inputOf right) ∧
      (∀ name term, model.languages name term ↔ ∃ rank, ranked.languages name rank term) ∧
      (∀ ambient term, InternedGuardedLanguage.meaning holds ambient left term ↔
        IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf left) term) ∧
      (∀ ambient term, InternedGuardedLanguage.meaning holds ambient right term ↔
        IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf right) term) := by
  let view := SourceRecursiveIntersectionInputView.view source holds
  let first := SourceRecursiveIntersectionInputView.inputOf left
  let second := SourceRecursiveIntersectionInputView.inputOf right
  have firstOriginal : SourceRecursiveIntersectionInputView.OriginalInput source first :=
    ⟨left, leftOriginal, leftAvailable, leftOriginal.codec left⟩
  have secondOriginal : SourceRecursiveIntersectionInputView.OriginalInput source second :=
    ⟨right, rightOriginal, rightAvailable, rightOriginal.codec right⟩
  have firstClosed : IntersectSchedule.closed view first = true := by
    rw [SourceRecursiveIntersectionInputView.closed_readback source facts holds left leftOriginal leftAvailable, leftClosed]
    rfl
  have secondClosed : IntersectSchedule.closed view second = true := by
    rw [SourceRecursiveIntersectionInputView.closed_readback source facts holds right rightOriginal rightAvailable, rightClosed]
    rfl
  let inputs := SourceRecursiveIntersectionInputView.finiteInput source facts holds first second
    firstOriginal secondOriginal firstClosed secondClosed
  refine ⟨IntersectSchedule.finiteInputMeaning view inputs, IntersectSchedule.finiteRankedInput view inputs,
    Or.inl (.root), Or.inr (.root), fun _ _ => Iff.rfl, ?_, ?_⟩
  · intro ambient term
    rw [SourceRecursiveIntersectionGuardedInput.input_exact source facts holds left leftOriginal leftAvailable leftClosed ambient]
    exact (IntersectSchedule.finiteLanguages_exact view inputs first (Or.inl .root) term).symm
  · intro ambient term
    rw [SourceRecursiveIntersectionGuardedInput.input_exact source facts holds right rightOriginal rightAvailable rightClosed ambient]
    exact (IntersectSchedule.finiteLanguages_exact view inputs second (Or.inr .root) term).symm

section ExactContextBoundary
local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Exact seen-pair equality cannot hold for every candidate at a new binder.
This refutes an induction hypothesis. It does not refute the source algorithm. -/
theorem unrestricted_extension_impossible (holds : SourceGuard → Term SourceSymbol → Bool)
    (source : InternedConstructorTemplates.State SourceSymbol SourceGuard)
    (input output : InternedGuardedLanguage.Env SourceSymbol)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : List Nat) (key : Nat × Nat) (symbol : SourceSymbol) :
    ¬ (∀ candidate : Lang SourceSymbol,
      SourceEqualityNativeDemandOpenMeaning.SeenContext holds source input
        (InternedGuardedLanguage.bind output (.intersection key.1 key.2) candidate)
        (SourceRecursiveIntersectionDomain.extend domain bindings key)) := by
  intro allCandidates
  have member := (SourceRecursiveIntersectionDomain.extend_seen domain bindings key key).mpr (Or.inl rfl)
  have empty := SourceEqualityNativeDemandOpenMeaning.seen_override_forces holds source input output
    (SourceRecursiveIntersectionDomain.extend domain bindings key) key member (fun _ => False) (allCandidates _)
  have full := SourceEqualityNativeDemandOpenMeaning.seen_override_forces holds source input output
    (SourceRecursiveIntersectionDomain.extend domain bindings key) key member (fun _ => True) (allCandidates _)
  have impossible : (False : Prop) = True := congrFun (empty.trans full.symm) (.node symbol [])
  exact impossible.symm ▸ True.intro

end ExactContextBoundary
end MicroCFTA.SourceCurrentAllocatedNativePairContexts
