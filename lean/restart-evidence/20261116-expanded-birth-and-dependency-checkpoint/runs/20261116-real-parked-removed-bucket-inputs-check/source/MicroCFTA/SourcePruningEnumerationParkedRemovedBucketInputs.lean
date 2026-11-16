import MicroCFTA.SourcePruningEnumerationRealEagerParkedRawBucketReceipt
import MicroCFTA.SourcePruningEnumerationCreatedIsolation
import MicroCFTA.SourcePruningEnumerationRecursivePacket

namespace MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open EnumerationDependencies EnumerationReferences InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

/-- Retain the original removed bucket at its actual real-worker parked restart. -/
theorem actual_parked_removed_bucket_inputs
    [DecidableEq Symbol] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel depth uv : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (metadata updated : Metadata Typing) (caller : Caller width) (memos : Memos)
    (before parked : Cached) (checked core : Core) (next : Option Next)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    ∃ (handle : Nat) (bucket : List Suspended) (readAfter : Core)
        (value : Node) (size : Nat) (resolved : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some handle) bucket, readAfter)] ∧
      before.core.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      InputsPending parked.core bucket ∧
      Avoids parked.core.representatives uv bucket ∧
      EnumerationDischargeHistory.IsolatedPending uv handle parked.core ∧
      UnionFind.Reaches before.core.representatives uv uv size ∧
      Frame before.core readAfter ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap workFuel uv handle bucket readAfter) =
          [.ok (true, checked)] ∧
      Success (representative workFuel uv) readAfter uv resolved ∧
      Frame readAfter resolved ∧
      recursionKey handle bucket ∈ before.core.recursionAncestry uv ∧
      resolved.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      Success (setValue uv (.unenumerated (some handle) [])) resolved () checked ∧
      checked = {resolved with values := resolved.values.set uv (.unenumerated (some handle) [])} ∧
      parked.core = checked ∧
      SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
        workFuel uv handle bucket before checked = some parked ∧
      ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
        [.ok ((updated, next), core)] ∧
      updated = metadata ∧ core = checked ∧
      next = SourcePruningEnumerationRestart.decision stop order metadata parked ∧
      SourcePruningEnumerationRestart.decision stop order metadata parked ≠ some .stuck ∧
      (∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
        ∀ other, UnionFind.SameClass checked.representatives sc.var other ↔
          UnionFind.SameClass before.core.representatives sc.var other) ∧
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
        metadata caller memos.query before (some (.expand uv)) =
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel depth
        updated caller memos.query (EnumerationExpandableIndex.frame core parked) next := by
  obtain ⟨ready, _incoming, _realized⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv packet.valid packet.safe chosen
  obtain ⟨handle, bucket, readAfter, value, root, size, resolved,
    reading, originalStored, path, readFrame, decoded, boundary, checking, resolution, resolvedFrame,
    seen, resolvedStored, written, shape, parkedCore, adapted, restarted,
    updatedEq, coreEq, nextEq, notStuck, aliases, restart⟩ :=
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.parked_singleton_removed_bucket_receipt
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth uv
      metadata updated caller memos.query before parked checked core next packet.safe.1.total actual
  obtain ⟨_rootSize, rootPath⟩ := ready.root
  have rootSame : root = uv := (UnionFind.reaches_unique path rootPath).1
  subst root
  have frames := readFrame.trans resolvedFrame
  have pendingBefore := pending_inputs before.core packet.pending uv (some handle) bucket originalStored
  have originalAvoid := ready.avoids handle bucket originalStored
  have clearOrigin := EnumerationDependencies.setValue_origin
    uv (.unenumerated (some handle) []) resolved checked
    (by intro produced impossible; cases impossible) written
  have originalExpanded : EnumeratedOrigin before.core checked := by
    intro slot fragment stored
    have previous := clearOrigin slot fragment stored
    simpa only [frames.values] using previous
  have classes : ∀ left right, UnionFind.SameClass checked.representatives left right ↔
      UnionFind.SameClass before.core.representatives left right := by
    intro left right
    rw [shape]
    change UnionFind.SameClass resolved.representatives left right ↔ _
    simp only [UnionFind.SameClass, frames.reaches]
  have pendingChecked : InputsPending checked bucket := by
    intro old oldFragment stored sc member related
    exact pendingBefore old oldFragment (originalExpanded old oldFragment stored)
      sc member ((classes old sc.var).mp related)
  have avoidChecked : Avoids checked.representatives uv bucket := by
    intro sc member related
    exact originalAvoid sc member ((classes uv sc.var).mp related)
  have pendingParked : InputsPending parked.core bucket := by
    rw [parkedCore]
    exact pendingChecked
  have avoidParked : Avoids parked.core.representatives uv bucket := by
    rw [parkedCore]
    exact avoidChecked
  have readSuccess : Success (getValue workFuel uv) before.core
      (.unenumerated (some handle) bucket) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap workFuel uv handle bucket) readAfter true checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  have isolated := EnumerationDischargeHistory.packet_parked_created_isolated
    formulas solver inventory caller memos metadata before parked stop order
    workFuel workFuel workFuel uv handle bucket readAfter checked packet chosen
    readSuccess checkSuccess adapted
  exact ⟨handle, bucket, readAfter, value, size, resolved,
    reading, originalStored, pendingParked, avoidParked, isolated,
    path, readFrame, decoded, boundary, checking, resolution, resolvedFrame,
    seen, resolvedStored, written, shape, parkedCore, adapted, restarted,
    updatedEq, coreEq, nextEq, notStuck, aliases, restart⟩

end MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs

#check MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs.actual_parked_removed_bucket_inputs
#print axioms MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs.actual_parked_removed_bucket_inputs
