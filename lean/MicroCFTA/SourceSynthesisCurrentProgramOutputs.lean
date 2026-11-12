import MicroCFTA.SourceSynthesisCurrentProgramSlotsInitialization
import MicroCFTA.SourceSynthesisCurrentProgramEnumerationWidth
import MicroCFTA.SourcePruningEnumerationInitialCarriers
import MicroCFTA.SourceSynthesisSharedPreparedProgramOutputs

/-!
# Program outputs from one current source initializer

The original input selects a sufficient mathematical enumeration width.
One initializer supplies the actual source value, caller and Program slots.
One shared prepared worker retains its full stable resources and every output.
Each output supplies its complete partial root and common Program projection.
This result does not assert output existence or adequate recursive depth.
It does not prove capacity at a fixed Haskell machine width.
-/
namespace MicroCFTA.SourceSynthesisCurrentProgramOutputs
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open EnumerationState (Graph)
open EnumerationCorrectness (Success NodeLanguage Satisfies)
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
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (run OutcomeResources emitted)
open SourceSynthesisOriginalSharedRankCompletion (seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- One current initializer and one no-stop worker retain their complete Program output receipts. -/
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
    let bits := SourceSynthesisCurrentProgramEnumerationWidth.enumBits lib query signed depth
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
          SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth initialSeed 0 ∧
    ∃ bound outcome,
      (
      (∀ extra, run holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order (bound + extra) depth
        metadata initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup = outcome) ∧
      OutcomeResources formulas solver initialCaller
        (SourcePruningEnumerationSharedPreparedReservation.final depth initialSeed 0) outcome ) ∧
      ∀ output ∈ emitted outcome, ∃ finalMarked : Nat → Prop,
        (∀ uv, uv = 0 → finalMarked uv) ∧ finalMarked 0 ∧
        SourceSynthesisProgramEnumerationRoles.ProgramSlots (Origin (encodedLibrary lib)) literal
          output.caller.checked.native.machine.heap output.cache.core finalMarked ∧
        output.metadata = none ∧
        EnumerationPureSelection.next (fun _ => none) output.cache = .done ∧
          ∃ (next : Inventory) (final : Memos) (outputMetadata : Metadata Typing),
            SourceCurrentAllocatedPartialInvariant.Post formulas solver next initialCaller output.caller final ∧
            final.query = output.queries ∧
            Packet formulas solver next output.caller final outputMetadata output.cache ∧
            (output.metadata = none ∨ output.metadata = some outputMetadata) ∧
            Fits (SourcePruningEnumerationSharedPreparedReservation.final depth initialSeed 0).2
              output.caller.checked ∧
            Heap (fun guard => guard ∈
              (SourcePruningEnumerationSharedPreparedReservation.final depth initialSeed 0).1)
              output.caller.checked.native.machine.heap ∧
            ∃ (level : Nat → Nat) (frontier : Nat),
              EnumerationOrder.Stratified output.cache.core level frontier ∧
              ∃ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                (after : EnumerationState.State Symbol Constraint),
                (∀ extra,
                  Success (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra))
                    output.cache.core actualPartial after ∧
                  ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra) output.cache.core) =
                    [.ok (actualPartial, after)]) ∧
                EnumerationDriver.RenderStable output.cache.core after ∧
                EnumerationCompressionFrame.Frame output.cache.core after ∧
                EnumerationOrder.Stratified after level frontier ∧
                (∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
                  (assignment : Nat → Language.Term Symbol),
                  Satisfies language meaning assignment output.cache.core →
                    Satisfies language meaning assignment after ∧
                    SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
                ∃ program, SourceSynthesisProgramTermSize.Projection literal Prod.fst
                    (SourcePruningPositions.openProgram true actualPartial) program ∧
                  ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
                    SourcePruningPartialMatch.Completes assignment actualPartial full →
                      SourceSynthesisProgramTermSize.Projection literal Prod.fst full program := by
  dsimp only
  let bits := SourceSynthesisCurrentProgramEnumerationWidth.enumBits lib query signed depth
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
  have reservation : SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth (seed heap) 0 :=
    SourceSynthesisCurrentProgramEnumerationWidth.enum_reserved_of_build
      lib query signed expression returned depth value heap built
  have startupSlots : ProgramSlots (Origin (encodedLibrary lib)) literal heap startup.core
      (fun uv => uv = 0) := slots
  have outputs := SourceSynthesisSharedPreparedProgramOutputs.run_finite_complete_resources_program_outputs
    holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges order formulas solver depth
    initialInventory initialCaller SourceCurrentAllocatedPartialInitialization.globals startup metadata
    (seed heap) 0 startupReceipt.1.1 initialFits initialHeap
    (fun _ _ _ _ _ member => member) (fun _ _ _ _ => Nat.le_refl _)
    (Nat.le_of_eq startupReceipt.1.2.2.2.1) reservation
    (Origin (encodedLibrary lib)) (fun uv => uv = 0) startupSlots rfl
  exact ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
    facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady,
    closed, original, valueFields, handle, encoded, decoded, slots,
    startupReceipt, initialFits, initialHeap, reservation, outputs⟩

end MicroCFTA.SourceSynthesisCurrentProgramOutputs
