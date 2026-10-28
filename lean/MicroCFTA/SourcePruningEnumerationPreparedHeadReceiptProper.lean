import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission
import MicroCFTA.SourcePruningEnumerationSelectedEdgeProper

/-!
# Proper storage at an actual completed prepared head

The original stored slot supplies inherited trie validity.
The separate prepared parent supplies availability and closedness.
The actual selected completion and captured finalizer preserve proper storage.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationProgress InternedConstructorTemplates
open EnumerationSemantics
open EnumerationSchedule EnumerationDependencies InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- The same completed prepared head preserves proper storage from its own input. -/
theorem CompletedHeadReceipt.proper
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {storedEdges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached} {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv handle scs parentEntry storedEdges depth free edge bound fragment reached saved after
      returnedInventory returnedMemos)
    (proper : ProperState before.core) : ProperState after.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := receipt.projected
  have stored := receipt.admission.stored
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    receipt.admission.ready.safe.1.values _ (List.mem_of_getElem? stored)
  have inputs : ProperInputs scs :=
    proper_inputs (.unenumerated (some handle) scs) (proper _ (List.mem_of_getElem? stored))
  have inheritedInputs : ValidSuspended scs := fun sc member => (inputs sc member).1
  have pending := EnumerationReferences.pending_inputs before.core receipt.admission.packet.pending
    uv (some handle) scs stored
  have completed := receipt.running 0
  simp only [Nat.add_zero] at completed
  unfold SourcePruningEnumerationCapturedEdge.run at completed
  cases selectedRun : SourcePruningEnumerationSelectedEdge.run checkEmpty bound bound bound bound bound
      scs edge caller before memos.query with
  | unhandled => rw [selectedRun] at completed; cases completed
  | rejected selectedCaller queries selectedCache => rw [selectedRun] at completed; cases completed
  | stopped fragments observation candidate => rw [selectedRun] at completed; cases completed
  | complete produced selectedCaller queries selectedCache =>
      rw [selectedRun] at completed
      simp only [Option.map_eq_some_iff] at completed
      obtain ⟨finished, finishRun, fields⟩ := completed
      have sameCache : finished = after :=
        (SourcePruningEnumerationSelectedEdge.Result.complete.inj fields).2.2.2
      rw [← sameCache]
      exact SourcePruningEnumerationFinalize.run_proper selectedCaller.checked.native.machine.heap bound uv
        produced selectedCache finished
        (SourcePruningEnumerationSelectedEdge.complete_proper caller before checkEmpty
          parentEntry storedEdges depth free edge scs roots memos receipt.admission.packet.context
          receipt.admission.parentAvailable receipt.admission.parentClosed receipt.admission.selected
          receipt.admission.ready.safe realized paths counts flags bounded pending receipt.allowed
          tries residual projected proper inheritedInputs selectedRun) finishRun

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
