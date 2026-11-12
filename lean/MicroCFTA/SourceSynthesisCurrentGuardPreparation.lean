import MicroCFTA.SourceSynthesisCurrentSourceGuards
import MicroCFTA.SourceEqualityOriginalAllocationPreparation
import MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory

/-!
# Equality-field preparation for current source construction

The current literal alphabet supplies normalized equality payloads.
The serial allocator returns its actual cache and complete receipt.
The supplied native build retains that same cache's conjunction fields.
This module does not construct another native value or initialize a worker.
-/
namespace MicroCFTA.SourceSynthesisCurrentGuardPreparation
open Cache InternedConstructorTemplates
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards)
local notation "Cached" => SourceEqualityGuardReadback.Cached

private theorem eqGuard_cached (classes : List (List (List Nat))) :
    Cached (eqGuard classes).equalities := by
  rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
  exact SourceEqualityGuardReadback.normalize_cached classes

private theorem alphabet_cached (lib : Library) (guard : Guard)
    (member : guard ∈ alphabet lib) : Cached guard.equalities := by
  simp only [alphabet, List.mem_cons, List.mem_append, List.mem_map] at member
  rcases member with rfl | rfl | rfl | ⟨entry, _included, rfl⟩ | ⟨entry, _included, rfl⟩
  · exact SourceEqualityConstraintConstructors.top_cached
  · exact eqGuard_cached _
  · exact eqGuard_cached _
  · exact eqGuard_cached _
  · exact eqGuard_cached _

/-- Every mapped guard of the actual current output has a normalized equality payload. -/
theorem mapped_guards_cached {Symbol : Type} (literal : String → Symbol)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression) :
    ∀ guard ∈ guards (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression),
      Cached guard.equalities := by
  intro guard member
  exact alphabet_cached (encodedLibrary lib) guard
    (SourceSynthesisCurrentSourceGuards.mapped_guards literal lib query signed expression returned guard member)

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

/-- Serial allocation derives its complete receipt and fields for the same actual native build. -/
theorem prepared_fields_of_build [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (initial : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid initial)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap) :
    ∃ fields cache,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (guards (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression)) initial fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap := by
  have cached : ∀ guard ∈ guards (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression),
      Cached guard.equalities := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
      mapped_guards_cached SourceSynthesisLabelProgramBuildRoles.literal lib query signed expression returned
  obtain ⟨fields, cache, prepared⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete _
    initial valid cached
  exact ⟨fields, cache, prepared, prepared.history.fields valid
    (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) (fun _ member => member) value heap built⟩

end MicroCFTA.SourceSynthesisCurrentGuardPreparation
