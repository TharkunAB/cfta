import MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport

#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.ranks_eq
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.languages_eq
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.reachable_mono
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_representative
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_valid
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_ranks
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_languages
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.Admitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.initial_admitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.advance_admitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.admitted_mono
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.node_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.edge_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.contextual
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.ranks_eq
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.languages_eq
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.reachable_mono
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_representative
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_valid
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_ranks
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.inventory_languages
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.Admitted
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.initial_admitted
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.advance_admitted
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.admitted_mono
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.node_law
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.edge_law
#check @MicroCFTA.SourceCurrentAllocatedNativeInputModelTransport.contextual

namespace MicroCFTA.InputModelTransportProbe
open Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open IntersectSchedule SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache SourceCurrentAllocatedNativePairContexts
open SourceCurrentAllocatedNativeInputModelTransport
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat}

section Inventories
variable (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
  (holds : Guard → Term Symbol → Bool) (before after : List (Value Symbol Guard))
  (beforeOriginal : ∀ value ∈ before, Original value) (beforeAvailable : Values source before)
  (beforeClosed : ∀ value ∈ before, value.free = [])
  (afterOriginal : ∀ value ∈ after, Original value) (afterAvailable : Values source after)
  (afterClosed : ∀ value ∈ after, value.free = [])
local notation "oldInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source facts holds
  before beforeOriginal beforeAvailable beforeClosed
local notation "newInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source facts holds
  after afterOriginal afterAvailable afterClosed

-- Literal root inclusion grows admission without changing any independent ranks or languages.
example (included : ∀ value ∈ before, value ∈ after) :
    (∀ input, (oldInputs).valid input → (newInputs).valid input) ∧
      finiteRanks (view source holds) oldInputs = finiteRanks (view source holds) newInputs ∧
      finiteLanguages (view source holds) oldInputs = finiteLanguages (view source holds) newInputs := by
  exact ⟨inventory_valid source facts holds before after beforeOriginal beforeAvailable beforeClosed
      afterOriginal afterAvailable afterClosed included, rfl, rfl⟩

-- Actual returned-cell admission prevents vacuous old laws from becoming new warm guarantees.
example (included : ∀ value ∈ before, value ∈ after) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (admitted : Admitted (view source holds) (finiteInputMeaning (view source holds) oldInputs) state)
    (valid : Contextual (view source holds) (finiteInputMeaning (view source holds) oldInputs)
      (finiteRankedInput (view source holds) oldInputs) holds state) :
    Contextual (view source holds) (finiteInputMeaning (view source holds) newInputs)
      (finiteRankedInput (view source holds) newInputs) holds state ∧
      Admitted (view source holds) (finiteInputMeaning (view source holds) newInputs) state := by
  exact ⟨contextual (view source holds) oldInputs newInputs rfl holds state admitted valid,
    admitted_mono (view source holds) (finiteInputMeaning (view source holds) oldInputs)
      (finiteInputMeaning (view source holds) newInputs) state
      (inventory_valid source facts holds before after beforeOriginal beforeAvailable beforeClosed
        afterOriginal afterAvailable afterClosed included) admitted⟩
end Inventories

-- Empty tables satisfy the old-domain coverage needed for transport into any same-representative model.
example (view : View Symbol) (before after : FiniteInput view)
    (same : before.representative = after.representative) (holds : Guard → Term Symbol → Bool)
    (machine : Machine Symbol Guard) :
    Contextual view (finiteInputMeaning view after) (finiteRankedInput view after) holds (initial width machine) :=
  contextual view before after same holds (initial width machine)
    (initial_admitted view (finiteInputMeaning view before) width machine)
    (initial_contextual view (finiteInputMeaning view before) (finiteRankedInput view before) holds width machine)

-- A vacuous old request law cannot justify a newly admitted request with a common term.
example (view : View Symbol) (before after : FiniteInput view) (holds : Guard → Term Symbol → Bool)
    (request : NodeRequest Symbol Guard)
    (notAdmitted : ¬NodeInputs view (finiteInputMeaning view before) request)
    (admitted : NodeInputs view (finiteInputMeaning view after) request)
    (emptySeen : request.domain.key.seen = []) (output : InternedGuardedLanguage.Env Symbol)
    (first second : Nat) (term : Term Symbol)
    (left : inputAt (finiteRankedInput view after).languages (inputOf request.left) first term)
    (right : inputAt (finiteRankedInput view after).languages (inputOf request.right) second term) :
    NodeLaw view (finiteInputMeaning view before) (finiteRankedInput view before) holds request .empty ∧
      ¬NodeLaw view (finiteInputMeaning view after) (finiteRankedInput view after) holds request .empty := by
  constructor
  · constructor
    · intro impossible
      exact False.elim (notAdmitted impossible)
    · intro impossible
      exact False.elim (notAdmitted impossible)
  · intro law
    simpa only [InternedGuardedLanguage.meaning] using law.complete admitted (first + second) output
      (complete_empty (finiteRankedInput view after).languages (first + second) request.domain.key output emptySeen)
      first second (Nat.le_refl _) term left right

end MicroCFTA.InputModelTransportProbe
