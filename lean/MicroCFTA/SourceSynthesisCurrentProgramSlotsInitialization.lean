import MicroCFTA.SourceSynthesisCurrentCallerInitialization
import MicroCFTA.SourceSynthesisProgramTypeFieldConstruction
import MicroCFTA.SourceSynthesisProgramEnumerationRoles

/-!
# Initial Program slots from one current source build

One current initializer retains its complete cold caller receipt.
The same build supplies all physical Type fields and its exact native handle.
Raw enumeration initialization marks only slot zero as a Program occurrence.
This result does not execute an enumeration worker.
-/
namespace MicroCFTA.SourceSynthesisCurrentProgramSlotsInitialization
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One current initializer derives all initial Program-slot roles at its same native root. -/
theorem accepted (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) initial fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (SourceCurrentAllocatedPartialInitialization.caller width cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
        ValueFields (Origin (encodedLibrary lib)) literal value ∧
        ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
          ProgramSlots (Origin (encodedLibrary lib)) literal heap
            (EnumerationState.initial handle) (fun uv => uv = 0) := by
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady, closed, original⟩ :=
    SourceSynthesisCurrentCallerInitialization.accepted lib query signed expression returned
      width initial valid formulas solver
  have valueFields := (SourceSynthesisProgramTypeFieldConstruction.current_root_fields
    lib query signed expression returned value heap built).2
  obtain ⟨handle, encoded, decoded⟩ := SourcePruningEnumerationNodes.available_readback
    heap value facts.coherent available closed
  exact ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady, closed,
    original, valueFields, handle, encoded, decoded,
    SourceSynthesisProgramEnumerationRoles.initial_program_slots heap handle value decoded valueFields⟩

end MicroCFTA.SourceSynthesisCurrentProgramSlotsInitialization
