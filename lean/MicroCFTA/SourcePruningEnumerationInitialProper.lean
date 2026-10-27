import MicroCFTA.SourcePruningEnumerationInitialPacket
import MicroCFTA.SourcePruningEnumerationPrefixAdmission
import MicroCFTA.EnumerationValidity
import MicroCFTA.EnumerationProgress

/-!
# Proper pending paths at literal native startup

The initial slot contains the actual closed available root value.
Native readback determines its handle and its expandable flag.
The initial storage, waiting counts and metadata derive the full packet.
The entire original startup packet remains. ProperState follows from the initial core.
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

/-- The complete original native startup packet also has proper pending paths. -/
theorem initial_packet_proper
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
      EnumerationProgress.ProperState startup.core := by
  obtain ⟨handle, encoded, decoded, packet, canonical, stored, mass, counts, flags⟩ :=
    initial_packet formulas solver inventory caller memos metadata value context available closed emptyPending
  exact ⟨handle, encoded, decoded, ⟨packet, canonical, stored, mass, counts, flags⟩,
    EnumerationProgress.initial_proper handle⟩

end MicroCFTA.SourcePruningEnumerationRecursive
