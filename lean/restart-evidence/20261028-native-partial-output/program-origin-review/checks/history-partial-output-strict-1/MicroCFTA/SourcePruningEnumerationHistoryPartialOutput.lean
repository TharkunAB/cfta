import MicroCFTA.SourcePruningEnumerationOutputRendering
import MicroCFTA.SourcePruningEnumerationPartialOutput
import MicroCFTA.SourcePruningEnumerationResourceHistoryCarriers

/-!
# Finite partial output at the same actual recursive history endpoint

The actual final tag supplies its full native packet and dependency order.
Original carrier provenance derives an allocated root at that endpoint.
Partial output permits pending holes and intentional recursive truncation.
No discharged output or satisfying model is an input admission.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open Language Fragments EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
variable {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
variable {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
variable {stop : Option (Metadata Typing → Nat → Bool)}
variable {order : Metadata Typing → List Nat → Option Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
variable {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
variable {next : Option Next} {output : Output (bits + 2) Typing}


/-- The same history constructs native partial output before every output-model observer. -/
theorem ResourceHistory.root_partial_complete_models
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (references : EnumerationGraphReferences.ReferencesCarry before.core)
    (carried : EnumerationCarriers.CarriesGraph before.core 0) :
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
  obtain ⟨finalInventory, finalMemos, finalMetadata, packet⟩ := history.output_packet
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  have provenance := history.carriers_output references
  have inside := EnumerationRenderability.carrier_inside output.cache.core packet.safe 0
    (provenance.1 0 carried)
  obtain ⟨bound, observedTerm, after, actual, stable, frame, afterOrder, models⟩ :=
    SourcePruningEnumerationPartialOutput.rootPartial_complete
      output.caller.checked.native.machine.heap level frontier output.cache.core packet.safe ordered inside
  refine ⟨finalInventory, finalMemos, finalMetadata, packet, level, frontier, ordered,
    bound, observedTerm, after, actual, stable, frame, afterOrder, ?_, models⟩
  exact callback_frame packet finalMetadata after stable.safe frame ⟨level, frontier, afterOrder⟩ (by
    intro group member entry listed
    rw [frame.counter]
    exact packet.bounded group member entry listed)

end MicroCFTA.SourcePruningEnumerationRecursive
