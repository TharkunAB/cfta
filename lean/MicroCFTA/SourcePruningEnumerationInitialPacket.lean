import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationPrefixAdmission
import MicroCFTA.EnumerationValidity

/-!
# The literal native enumeration startup packet

The initial slot contains the actual closed available root value.
Native readback determines its handle and its expandable flag.
The initial storage, waiting counts and metadata derive the full packet.
No graph interpretation or desired packet is an admission.
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

/-- Original native admission derives the exact initialized packet, root and both indexes. -/
theorem initial_packet
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
      Packet formulas solver inventory caller memos metadata startup ∧
      EnumerationValidity.Canonical startup.core ∧
      startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
      EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
      ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot) := by
  have coherent := context.ready.good.heap.semantic.1.normal.facts.coherent
  obtain ⟨handle, encoded, decoded⟩ := available_readback
    caller.checked.native.machine.heap value coherent available closed
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
      fun _ => none⟩
  have realized : PendingRealized caller.checked.native.machine.heap startup.core := by
    intro slot storedNode scs stored
    cases slot with
    | zero =>
        simp [startup, EnumerationState.initial] at stored
        obtain ⟨rfl, rfl⟩ := stored
        exact ⟨value, decoded, available, closed⟩
    | succ slot => simp [startup, EnumerationState.initial] at stored
  have counts : EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting :=
    EnumerationCanonicalWaiting.initial_correct (fun uv => uv) handle
  have flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot) := by
    intro slot
    cases slot with
    | zero => simp [startup, EnumerationState.initial, SourcePruningEnumerationNativeIndex.candidate, decoded]
    | succ slot => simp [startup, EnumerationState.initial, SourcePruningEnumerationNativeIndex.candidate]
  have packet : Packet formulas solver inventory caller memos metadata startup := by
    refine ⟨context, ⟨initial_storage handle, initial_live handle⟩, EnumerationReferences.initial_pending handle,
      ⟨(fun uv => uv), ?_, initial_storage handle, realized, counts, flags⟩,
      ⟨(fun _ => 0), 0, EnumerationOrder.initial_stratified handle⟩, ?_⟩
    · intro uv
      exact ⟨1, .root (UnionFind.read_initial [0] uv)⟩
    · intro group member
      rw [emptyPending] at member
      exact False.elim (List.not_mem_nil member)
  exact ⟨handle, encoded, decoded, packet, EnumerationValidity.initial_canonical handle,
    rfl, rfl, counts, flags⟩

end MicroCFTA.SourcePruningEnumerationRecursive
