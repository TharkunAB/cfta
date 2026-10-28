import MicroCFTA.SourcePruningEnumerationOutputRenderCoverage
import MicroCFTA.SourcePruningEnumerationResourceHistoryCarriers
import MicroCFTA.SourcePruningEnumerationRenderCoverage

/-!
# Actual output rendering from original carrier provenance

The same resource history retains original graph-bearing classes and references.
Only output discharge remains as a structural rendering condition.
The entire actual output packet and rendering result remain present.
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


/-- Original provenance and actual output discharge construct the same native render. -/
theorem ResourceHistory.render_complete_models_from_origin
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (marker : Symbol) (uv : Nat)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core)
    (references : EnumerationGraphReferences.ReferencesCarry before.core)
    (carried : EnumerationCarriers.CarriesGraph before.core uv) :
    ∃ (finalInventory : Inventory) (finalMemos : Memos) (finalMetadata : Metadata Typing),
      Packet formulas solver finalInventory output.caller finalMemos finalMetadata output.cache ∧
      ∃ (level : Nat → Nat) (frontier : Nat),
        EnumerationOrder.Stratified output.cache.core level frontier ∧
        ∃ (bound : Nat) (term : Term Symbol) (pending : List (Constraint × Term Symbol))
      (after : EnumerationState.State Symbol Constraint),
      (∀ extra, Success (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker (bound + extra) uv) output.cache.core (term, pending) after) ∧
      EnumerationDriver.RenderStable output.cache.core after ∧ EnumerationCompressionFrame.Frame output.cache.core after ∧ EnumerationOrder.Stratified after level frontier ∧
      ∀ (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
        (assignment : Nat → Term Symbol),
        Satisfies language meaning assignment output.cache.core →
        term = assignment uv ∧
        pending = output.cache.core.obligations.map (fun obligation => (obligation.1, fill assignment obligation.2)) ∧
        (∀ obligation ∈ pending, meaning obligation.1 obligation.2) ∧
        Satisfies language meaning assignment after := by
  obtain ⟨preserved, outputReferences⟩ := history.carriers_output references
  exact history.render_complete_models marker uv discharged outputReferences (preserved uv carried)

end MicroCFTA.SourcePruningEnumerationRecursive
