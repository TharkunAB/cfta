import MicroCFTA.SourceSynthesisCurrentProgramStructure
import MicroCFTA.SourceSynthesisCurrentGuardPreparation
import MicroCFTA.SourceSynthesisCurrentNativeGuardOrigins
import MicroCFTA.SourceCurrentAllocatedPartialInitialization

/-!
# Cold callers from current signed source output

Current source success supplies one actual native build. Its observers derive
Program roles, guard origins, and equality-field preparation on that same build.
The returned cache initializes the full cold caller Context.
This module does not execute a worker or establish hereditary Type fields.
-/
namespace MicroCFTA.SourceSynthesisCurrentCallerInitialization
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Current output constructs its own build, preparation, physical roles, and full cold Context. -/
theorem accepted (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) initial fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue SourceSynthesisLabelProgramBuildRoles.literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (SourceCurrentAllocatedPartialInitialization.caller width cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨value, heap, built⟩ :=
    InternedFreshOrdinaryClosedCompletion.closed_complete (ordinarySymbols expression)
  have verified := InternedFreshOrdinaryFacts.closed_verified (ordinarySymbols expression)
  have facts : Facts heap := by
    simpa only [built, Outcome.state] using verified.facts
  have available := verified.result value heap built
  have mappedBuilt : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisProgramBuildRolesGeneric.mapSyntax SourceSynthesisLabelProgramBuildRoles.literal expression)
      [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have sourceStructure :=
    SourceSynthesisCurrentProgramStructure.current_root_structure lib query signed expression returned
  have roles := SourceSynthesisProgramBuildRolesGeneric.build_mapped_program
    SourceSynthesisLabelProgramBuildRoles.literal expression sourceStructure.1
    [] empty value heap empty_facts (by intro child member; cases member) mappedBuilt
  obtain ⟨fields, cache, prepared, conjunctionFields⟩ :=
    SourceSynthesisCurrentGuardPreparation.prepared_fields_of_build lib query signed expression returned
      initial valid value heap built
  have initialized := SourceCurrentAllocatedPartialInitialization.constructed width prepared.history valid
    (ordinarySymbols expression) (fun _ member => member) value heap built formulas solver
  obtain ⟨identity, emptySame, emptyReady, _available, closed, original⟩ := initialized.2
  have growth : Grows empty heap := by
    simpa only [built, Outcome.state] using verified.growth
  have issued : Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued := by
    simpa only [built, Outcome.state] using verified.history
  have origins := SourceSynthesisCurrentNativeGuardOrigins.constructed
    SourceSynthesisLabelProgramBuildRoles.literal lib query signed expression returned value heap mappedBuilt
  exact ⟨fields, cache, value, heap, built, prepared, conjunctionFields, initialized.1,
    facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady, closed, original⟩

end MicroCFTA.SourceSynthesisCurrentCallerInitialization
