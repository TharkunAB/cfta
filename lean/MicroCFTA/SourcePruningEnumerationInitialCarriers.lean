import MicroCFTA.SourcePruningEnumerationInitialPacket
import MicroCFTA.EnumerationRenderability

/-!
# Native startup supplies graph-bearing root and reference provenance

The complete original startup packet remains present.
Its literal root supplies a carrier and has no stored fragment holes.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Original native startup also supplies root and reference carriers. -/
theorem initial_packet_carriers
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (value : Node)
    (context : Context formulas solver inventory caller memos)
    (available : Available caller.checked.native.machine.heap value)
    (closed : value.free = []) (emptyPending : metadata.pending = []) :
    ∃ handle,
      encodeNode value = some handle ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      let startup : Cached :=
        ⟨EnumerationState.initial handle,
          fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
          fun _ => none⟩
      (Packet formulas solver inventory caller memos metadata startup ∧
      EnumerationValidity.Canonical startup.core ∧
      startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
      EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
      ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot)) ∧
      EnumerationCarriers.CarriesGraph startup.core 0 ∧
      EnumerationGraphReferences.ReferencesCarry startup.core := by
  obtain ⟨handle, encoded, decoded, retained⟩ :=
    initial_packet formulas solver inventory caller memos metadata value context available closed emptyPending
  refine ⟨handle, encoded, decoded, retained, ?_, ?_⟩
  · exact EnumerationCarriers.carries_self (EnumerationState.initial handle)
      (initial_storage handle).total 0 (.unenumerated (some handle) []) rfl trivial
  · exact EnumerationRenderability.initial_references handle

end MicroCFTA.SourcePruningEnumerationRecursive
