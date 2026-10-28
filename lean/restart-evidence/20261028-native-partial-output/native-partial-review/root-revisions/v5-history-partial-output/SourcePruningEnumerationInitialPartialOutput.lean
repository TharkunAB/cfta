import MicroCFTA.SourcePruningEnumerationInitialRenderProper
import MicroCFTA.SourcePruningEnumerationOutputRenderOrigin
import MicroCFTA.EnumerationRenderability
import MicroCFTA.SourcePruningEnumerationResourceHistoryProper
import MicroCFTA.SourcePruningEnumerationHistoryPartialOutput

/-!
# Native partial output for every actual output from original startup

The complete old startup and concrete-render contract remains first.
The same actual resource history constructs a partial root observation.
Its bound, partial term, full state and packet precede every semantic model.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open Language Fragments EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the full original startup contract and construct partial output at every emitted cache. -/
theorem run_initial_finite_render_sound_partial
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (value : Node)
    (seed : Seed) (ceiling : Nat)
    (context : Context formulas solver inventory caller memos)
    (available : Available caller.checked.native.machine.heap value)
    (closed : value.free = []) (emptyPending : metadata.pending = [])
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling)
    (arity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    ∃ handle,
      encodeNode value = some handle ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      let before : Cached :=
        ⟨EnumerationState.initial handle,
          fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
          fun _ => none⟩
    ∃ bound outcome,
      ((((∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome, Canonical output.cache.core) ∧
      ∀ (_extra : Nat) output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ∀ (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (fuel : Nat)
          (after : Core) (term : Language.Term Symbol) (pending : List (Constraint × Language.Term Symbol)),
        SourcePruningEnumerationRendering.Discharged output.cache.core →
        Success (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker fuel 0)
          output.cache.core (term, pending) after →
        (∀ obligation ∈ pending, SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) →
        ∃ assignment : Nat → Language.Term Symbol,
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment before.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ∧
          (∀ sc ∈ ([] : List Suspended), Suspended.Holds assignment term sc) ∧ term = assignment 0 ∧
          EnumerationCompressionFrame.Frame output.cache.core after ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient output.caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment output.cache.core ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient output.caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment after) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        EnumerationProgress.ProperState output.cache.core)) ∧
      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        EnumerationCarriers.CarriesGraph output.cache.core 0 ∧
        EnumerationGraphReferences.ReferencesCarry output.cache.core ∧
        ∀ marker : Symbol, SourcePruningEnumerationRendering.Discharged output.cache.core →
    ∃ (finalInventory : Inventory) (finalMemos : Memos) (finalMetadata : Metadata Typing),
      Packet formulas solver finalInventory output.caller finalMemos finalMetadata output.cache ∧
      ∃ (level : Nat → Nat) (frontier : Nat),
        EnumerationOrder.Stratified output.cache.core level frontier ∧
        ∃ (bound : Nat) (term : Term Symbol) (pending : List (Constraint × Term Symbol))
      (after : EnumerationState.State Symbol Constraint),
      (∀ extra, Success (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker (bound + extra) 0) output.cache.core (term, pending) after) ∧
      EnumerationDriver.RenderStable output.cache.core after ∧ EnumerationCompressionFrame.Frame output.cache.core after ∧ EnumerationOrder.Stratified after level frontier ∧
      ∀ (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
        (assignment : Nat → Term Symbol),
        Satisfies language meaning assignment output.cache.core →
        term = assignment 0 ∧
        pending = output.cache.core.obligations.map (fun obligation => (obligation.1, fill assignment obligation.2)) ∧
        (∀ obligation ∈ pending, meaning obligation.1 obligation.2) ∧
        Satisfies language meaning assignment after) ∧
      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
    ∃ (finalInventory : Inventory) (finalMemos : Memos) (finalMetadata : Metadata Typing),
      Packet formulas solver finalInventory output.caller finalMemos finalMetadata output.cache ∧
      ∃ (level : Nat → Nat) (frontier : Nat),
        EnumerationOrder.Stratified output.cache.core level frontier ∧
        ∃ (bound : Nat) (observedTerm : Term (PartialSymbol Symbol)) (after : Core),
          (∀ extra,
            Success (SourcePruningEnumerationPartialOutput.rootPartial
              output.caller.checked.native.machine.heap (bound + extra))
              output.cache.core observedTerm after ∧
            ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
              output.caller.checked.native.machine.heap (bound + extra) output.cache.core) =
              [.ok (observedTerm, after)]) ∧
          EnumerationDriver.RenderStable output.cache.core after ∧
          EnumerationCompressionFrame.Frame output.cache.core after ∧
          EnumerationOrder.Stratified after level frontier ∧
          Packet formulas solver finalInventory output.caller finalMemos finalMetadata
            (EnumerationExpandableIndex.frame after output.cache) ∧
          ∀ (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
            (assignment : Nat → Term Symbol),
            Satisfies language meaning assignment output.cache.core →
              Satisfies language meaning assignment after ∧
              SourcePruningPartialMatch.Completes assignment observedTerm (assignment 0) := by
  obtain ⟨handle, encoded, decoded, bound, outcome, retained⟩ :=
    run_initial_finite_render_sound_carriers holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos metadata value seed ceiling context available
      closed emptyPending bounded known selectionMembers selectionLength reserved arity
  refine ⟨handle, encoded, decoded, bound, outcome, retained, ?_⟩
  have initialReferences : EnumerationGraphReferences.ReferencesCarry (EnumerationState.initial handle : Core) :=
    EnumerationRenderability.initial_references handle
  have rootCarrier : EnumerationCarriers.CarriesGraph (EnumerationState.initial handle : Core) 0 :=
    EnumerationCarriers.carries_self (EnumerationState.initial handle) (initial_storage handle).total
      0 (.unenumerated (some handle) []) rfl trivial
  intro output member
  have history := retained.1.1.2.2.1 0 output member
  exact history.root_partial_complete_models initialReferences rootCarrier

end MicroCFTA.SourcePruningEnumerationRecursive
