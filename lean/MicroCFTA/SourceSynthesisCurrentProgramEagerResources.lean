import MicroCFTA.SourceSynthesisCurrentProgramSlotsInitialization
import MicroCFTA.SourceSynthesisCurrentProgramEagerEnumerationWidth
import MicroCFTA.SourcePruningEnumerationInitialCarriers
import MicroCFTA.SourceSynthesisSharedEagerOutputControl

/-!
# Current source initialization and eager resource execution

One current initializer supplies the complete source and native receipt.
The source input selects one sufficient mathematical eager-plan width.
One actual eager producer retains the complete resource outcome.
Every emitted noStop output has no metadata and selects done.
This observer does not assert final Program roles or model existence.
-/
namespace MicroCFTA.SourceSynthesisCurrentProgramEagerResources
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open EnumerationState (Graph)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (OutcomeResources emitted)
open SourceSynthesisOriginalSharedRankCompletion (seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Current input and one computed width give stable actual eager resources and output control. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (order : Metadata Typing → List Nat → Option Nat) :
    let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
        ValueFields (Origin (encodedLibrary lib)) literal value ∧
        ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
          ProgramSlots (Origin (encodedLibrary lib)) literal heap
            (EnumerationState.initial handle) (fun uv => uv = 0) ∧
          let startup : Cached :=
            ⟨EnumerationState.initial handle,
              fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
              fun _ => none⟩
          let initialCaller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap
          let initialSeed := seed heap
          ((Packet formulas solver
              (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
              initialCaller SourceCurrentAllocatedPartialInitialization.globals metadata startup ∧
            EnumerationValidity.Canonical startup.core ∧
            startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
            SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
            EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
            ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
              ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot)) ∧
            EnumerationCarriers.CarriesGraph startup.core 0 ∧
            EnumerationGraphReferences.ReferencesCarry startup.core) ∧
          Fits initialSeed.2 initialCaller.checked ∧
          Heap (fun guard => guard ∈ initialSeed.1) heap ∧
          SourcePruningEnumerationSharedEagerReservation.eagerReserved bits depth initialSeed 0 ∧
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager
        holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order
        (bound + extra) depth metadata initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup = outcome) ∧
      OutcomeResources formulas solver initialCaller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal depth initialSeed 0) outcome ∧
      ∀ output ∈ emitted outcome,
        output.metadata = none ∧ EnumerationPureSelection.next (fun _ => none) output.cache = .done
    := by
  dsimp only
  let bits := SourceSynthesisCurrentProgramEagerEnumerationWidth.enumBits lib query signed depth
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
      closed, original, valueFields, handle, encoded, decoded, slots⟩ :=
    SourceSynthesisCurrentProgramSlotsInitialization.accepted lib query signed expression returned
      (bits + 2) Cache.emptyState Cache.empty_valid formulas solver
  let initialCaller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap
  let initialInventory :=
    SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
      fun _ => none⟩
  obtain ⟨initialHandle, initialEncoded, _initialDecoded, startupReceipt⟩ :=
    SourcePruningEnumerationRecursive.initial_packet_carriers formulas solver initialInventory
      initialCaller SourceCurrentAllocatedPartialInitialization.globals metadata value
      context available closed emptyPending
  have handleSame : initialHandle = handle := Option.some.inj (initialEncoded.symm.trans encoded)
  subst initialHandle
  have initialFits : Fits (seed heap).2 initialCaller.checked :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩
  have initialHeap : Heap (fun guard => guard ∈ (seed heap).1) heap :=
    SourceCurrentConjunctionGuardUniverse.initial heap facts
  have reservation : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits depth (seed heap) 0 :=
    SourceSynthesisCurrentProgramEagerEnumerationWidth.eager_reserved_of_build
      lib query signed expression returned depth value heap built
  obtain ⟨bound, outcome, running, resources⟩ :=
    SourcePruningEnumerationSharedEagerReservation.runEager_finite_complete_resources
      holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order
      formulas solver depth initialInventory initialCaller SourceCurrentAllocatedPartialInitialization.globals
      startup metadata (seed heap) 0 startupReceipt.1.1 initialFits initialHeap
      (fun _ _ _ _ _ member => member) (fun _ _ _ _ => Nat.le_refl _)
      (Nat.le_of_eq startupReceipt.1.2.2.2.1) reservation
  have control : ∀ output ∈ emitted outcome,
      output.metadata = none ∧ EnumerationPureSelection.next (fun _ => none) output.cache = .done := by
    intro output member
    have actualMember : output ∈ emitted
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates
          checkEmpty InternedEdgeResidency.nodeEdges none order (bound + 0) depth metadata initialCaller
          SourceCurrentAllocatedPartialInitialization.globals.query startup) := by
      rw [running 0]
      exact member
    have observed := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager_output_control
      holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order
      (bound + 0) depth metadata initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup
      output actualMember
    have noMetadata := observed.2 rfl
    exact ⟨noMetadata, observed.1 noMetadata⟩
  exact ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
    closed, original, valueFields, handle, encoded, decoded, slots,
    startupReceipt, initialFits, initialHeap, reservation, bound, outcome, running, resources, control⟩

end MicroCFTA.SourceSynthesisCurrentProgramEagerResources
