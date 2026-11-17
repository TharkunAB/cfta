import MicroCFTA.SourcePruningEnumerationCausalHistoryInputInvariants
import MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs

namespace MicroCFTA.SourcePruningEnumerationQualifiedParkedClear
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open EnumerationDependencies EnumerationReferences EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationRealEagerCausalOutputHistory
open SourcePruningEnumerationCausalHistoryInputInvariants
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow)
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

/- Note [One qualified head clear and its original bucket]
The event data come from one elimination of the qualified derivation.
The head classifier names only an actual parked runtime tag.
It supplies no future clear correctness or continuation law.
Ready, PendingReferences and IncomingAvoid concern the same entry cache.
The Packet corollary derives them from the actual restart choice.
The original indexed output receipt follows the literal real restart equality.
The retained output index is unchanged, including duplicate outputs.

Canonical and Total alone do not imply these semantic entry facts.
The qualification does not transport Packet to arbitrary later events.
A history proof index does not identify hidden constructor witnesses.
Consumers must keep the qualified event bundle together.
The proof adds no runtime fuel and makes no joint-model claim.
-/

/-- Retain one head clear, its original bucket and its exact indexed real continuation. -/
def QualifiedHeadParkedClearAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth uv : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached)
    (index : Nat) (output : Output (bits + 2) Typing) : Prop :=
  ∃ (updated : Metadata Typing) (parked : Cached) (checked core : Core) (next : Option Next)
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth updated caller queries (EnumerationExpandableIndex.frame core parked) next index output),
    QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail ∧
    (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
      (EnumerationExpandableIndex.frame core parked) next))[index]? = some output ∧
    SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parked) (some [.ok ((updated, next), core)]) ∧
    CanonicalTotal before.core ∧ CanonicalTotal checked ∧ CanonicalTotal parked.core ∧
    CanonicalTotal (EnumerationExpandableIndex.frame core parked).core ∧
    ∃ (handle : Nat) (bucket : List Suspended) (readAfter : Core)
        (value : Node) (size : Nat) (resolved : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some handle) bucket, readAfter)] ∧
      before.core.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      ValidSuspended bucket ∧
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
        metadata caller queries before (some (.expand uv)) =
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel depth
        updated caller queries (EnumerationExpandableIndex.frame core parked) next

private theorem ready_parked_removed_bucket_inputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth uv : Nat)
    (metadata updated : Metadata Typing) (caller : Caller (bits + 2)) (queries : Queries)
    (before parked : Cached) (checked core : Core) (next : Option Next)
    (ready : EnumerationDriver.Ready uv before.core)
    (pending : PendingReferences before.core) (incoming : IncomingAvoid uv before.core)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
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
        metadata caller queries before (some (.expand uv)) =
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel depth
        updated caller queries (EnumerationExpandableIndex.frame core parked) next := by
  obtain ⟨handle, bucket, readAfter, value, root, size, resolved,
    reading, originalStored, path, readFrame, decoded, boundary, checking, resolution, resolvedFrame,
    seen, resolvedStored, written, shape, parkedCore, adapted, restarted,
    updatedEq, coreEq, nextEq, notStuck, aliases, restart⟩ :=
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.parked_singleton_removed_bucket_receipt
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth uv
      metadata updated caller queries before parked checked core next ready.safe.1.total actual
  obtain ⟨_rootSize, rootPath⟩ := ready.root
  have rootSame : root = uv := (UnionFind.reaches_unique path rootPath).1
  subst root
  have frames := readFrame.trans resolvedFrame
  have pendingBefore := pending_inputs before.core pending uv (some handle) bucket originalStored
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
  have readReady := (EnumerationDriver.getValue_ready workFuel uv before.core readAfter
    (.unenumerated (some handle) bucket) ready readSuccess).1
  have readIncoming := EnumerationPendingReplacement.frame_incoming uv before.core readAfter readFrame incoming
  have checkedIsolated := EnumerationDischargeHistory.checkRepeated_created_isolated
    caller.checked.native.machine.heap workFuel uv handle bucket readAfter checked
    readReady readIncoming checkSuccess
  have isolated : EnumerationDischargeHistory.IsolatedPending uv handle parked.core := by
    rw [parkedCore]
    exact checkedIsolated
  exact ⟨handle, bucket, readAfter, value, size, resolved,
    reading, originalStored, pendingParked, avoidParked, isolated,
    path, readFrame, decoded, boundary, checking, resolution, resolvedFrame,
    seen, resolvedStored, written, shape, parkedCore, adapted, restarted,
    updatedEq, coreEq, nextEq, notStuck, aliases, restart⟩

theorem qualified_head_parked_removed_bucket_inputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth uv : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached)
    (index : Nat) (output : Output (bits + 2) Typing)
    (history : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      (depth + 1) metadata caller queries before (some (.expand uv)) index output)
    (qualified : QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history)
    (ready : EnumerationDriver.Ready uv before.core)
    (pending : PendingReferences before.core) (incoming : IncomingAvoid uv before.core)
    (observed : (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
      metadata caller queries before (some (.expand uv))))[index]? = some output)
    (parkedTag : match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries with
      | .parked .. => True
      | _ => False) :
    QualifiedHeadParkedClearAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel depth uv metadata caller queries before index output
 := by
  cases qualified with
  | parked actual tail input checkedFacts candidateFacts callbackFacts qualifiedTail =>
      obtain ⟨handle, bucket, readAfter, value, size, resolved,
        reading, stored, pendingParked, avoidParked, isolated,
        path, readFrame, decoded, boundary, checking, resolution, resolvedFrame,
        seen, resolvedStored, written, shape, parkedCore, adapted, restarted,
        updatedEq, coreEq, nextEq, notStuck, aliases, restart⟩ :=
        ready_parked_removed_bucket_inputs holeKey fits admits graph templates checkEmpty edgesOf stop order
          workFuel depth uv metadata _ caller queries before _ _ _ _ ready pending incoming actual
      have bucketValid := input.1 _ (List.mem_of_getElem? stored)
      change ValidSuspended bucket at bucketValid
      have suffixObserved := observed
      rw [restart] at suffixObserved
      exact ⟨_, _, _, _, _, tail, qualifiedTail, suffixObserved, actual,
        input, checkedFacts, candidateFacts, callbackFacts,
        handle, bucket, readAfter, value, size, resolved,
        reading, stored, bucketValid, pendingParked, avoidParked, isolated,
        path, readFrame, decoded, boundary, checking, resolution, resolvedFrame,
        seen, resolvedStored, written, shape, parkedCore, adapted, restarted,
        updatedEq, coreEq, nextEq, notStuck, aliases, restart⟩
  | selected actual _actionContinues _preparedHistory _input _checkedFacts _candidateFacts _qualifiedPreparation =>
      unfold SourcePruningEnumerationSelectedStep.runPrefix at parkedTag
      rw [actual] at parkedTag
      exact False.elim parkedTag

theorem actual_head_parked_removed_bucket_inputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth uv : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (metadata : Metadata Typing) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (index : Nat) (output : Output (bits + 2) Typing)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (canonical : Canonical before.core)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (observed : (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
      metadata caller memos.query before (some (.expand uv))))[index]? = some output)
    (parkedTag : match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query with
      | .parked .. => True
      | _ => False) :
    QualifiedHeadParkedClearAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel depth uv metadata caller memos.query before index output
 := by
  obtain ⟨history, qualified⟩ := resumeWithNarrow_real_eager_qualified_output_history
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
    metadata caller memos.query before (some (.expand uv)) index output
    canonical packet.safe.1.total observed
  obtain ⟨ready, incoming, _realized⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv packet.valid packet.safe chosen
  exact qualified_head_parked_removed_bucket_inputs holeKey fits admits graph templates checkEmpty edgesOf
    stop order workFuel depth uv metadata caller memos.query before index output history qualified
    ready packet.pending incoming observed parkedTag

end MicroCFTA.SourcePruningEnumerationQualifiedParkedClear
