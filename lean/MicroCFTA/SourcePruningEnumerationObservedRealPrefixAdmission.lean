import MicroCFTA.SourcePruningEnumerationObservedRealPrefixResources
import MicroCFTA.SourcePruningEnumerationSharedParkedRawBucketReceipt
import MicroCFTA.SourcePruningEnumerationPrefixMass

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem actual_narrowed_selected_bucket
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (workFuel selected oldHandle newHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (before readAfter checked after : Core)
    (ready : EnumerationDriver.Ready selected before)
    (incoming : EnumerationReferences.IncomingAvoid selected before)
    (reading : Success (getValue workFuel selected) before (.unenumerated (some oldHandle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap workFuel selected oldHandle scs)
      readAfter false checked)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata workFuel selected oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata workFuel workFuel
      selected oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (executed : Success action checked () after) :
    EnumerationReferences.IncomingAvoid selected after ∧
    before.values[selected]? = some (.unenumerated (some oldHandle) scs) ∧
    after.values[selected]? = some (.unenumerated (some newHandle) scs) := by
  have readFrame := (getValue_frame workFuel selected before readAfter _ ready.safe.1.total reading).1
  have readStored := (EnumerationDriver.getValue_root workFuel selected before readAfter _
    ready.safe ready.inside ready.root reading).2.2.2
  have originalStored : before.values[selected]? = some (.unenumerated (some oldHandle) scs) := by
    simpa only [readFrame.values] using readStored
  have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap workFuel
    selected oldHandle scs readAfter checked (readFrame.total ready.safe.1.total) checking
  have wholeFrame := readFrame.trans checkFrame
  have checkedStored : checked.values[selected]? = some (.unenumerated (some oldHandle) scs) := by
    simpa only [wholeFrame.values] using originalStored
  have checkedIncoming := EnumerationPendingReplacement.frame_incoming selected before checked wholeFrame incoming
  have selectedAction := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
    workFuel workFuel selected oldHandle newHandle scs oldValue value heap nextHeap narrowed nonempty encoded
  rw [prepared] at selectedAction
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative workFuel selected >>= fun root =>
          setValue root (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (congrArg Prod.snd (MergedSourceComparison.Result.done.inj selectedAction).1)
  rw [actionSame] at executed
  by_cases sameHandle : newHandle = oldHandle
  · rw [ite_eq_left sameHandle] at executed
    obtain ⟨_unit, afterSame⟩ := (success_pure () () checked after).mp executed
    subst after
    exact ⟨checkedIncoming, originalStored, by simpa only [sameHandle] using checkedStored⟩
  · rw [ite_eq_right sameHandle] at executed
    obtain ⟨root, resolved, resolution, writing⟩ := (success_bind _ _ _ _ _).mp executed
    have resolvedFrame := representative_frame workFuel selected root checked resolved
      (wholeFrame.total ready.safe.1.total) resolution
    have finalFrame := wholeFrame.trans resolvedFrame
    obtain ⟨found, lookup, rootSame, _stateSame⟩ :=
      (representative_success workFuel selected checked resolved root).mp resolution
    have reached := (UnionFind.findRoot_correct workFuel checked.representatives selected found lookup).1
    have rootSelected : root = selected := rootSame.trans
      (UnionFind.reaches_unique reached
        ((wholeFrame.reaches selected selected ready.root.choose).mpr ready.root.choose_spec)).1
    have resolvedStored : resolved.values[root]? = some (.unenumerated (some oldHandle) scs) := by
      simpa only [finalFrame.values, rootSelected] using originalStored
    have resolvedIncoming := EnumerationPendingReplacement.frame_incoming selected before resolved finalFrame incoming
    have finalIncoming := EnumerationPendingReplacement.setValue_incoming selected root (some oldHandle)
      (some newHandle) scs resolved after resolvedStored resolvedIncoming writing
    have shape := (EnumerationDriver.modify_success _ resolved after).mp writing
    have inside : root < resolved.values.length := (List.getElem?_eq_some_iff.mp resolvedStored).1
    have finalStored : after.values[root]? = some (.unenumerated (some newHandle) scs) := by
      rw [shape]
      exact List.getElem?_set_self inside
    exact ⟨finalIncoming, originalStored, by simpa only [rootSelected] using finalStored⟩

private theorem actual_parked_phase_admission
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (workFuel selected ceiling : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected))
    (originalMass : suspendedBound before.core ≤ ceiling)
    {checked restartCore : Core} {after : Cached} {updated : Metadata Typing}
    {next : Option Next}
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query =
        .parked checked (some after) (some [.ok ((updated, next), restartCore)])) :
    EnumerationReferences.IncomingAvoid selected after.core ∧
    suspendedBound after.core ≤ suspendedBound before.core ∧ suspendedBound after.core ≤ ceiling := by
  obtain ⟨_ready, incoming, _stored⟩ := SourcePruningEnumerationRestart.selected stop order metadata
    caller before selected packet.valid packet.safe chosen
  obtain ⟨oldHandle, scs, readAfter, _value, root, _size, resolved,
      reading, _originalStored, _path, readFrame, _decoded, _boundary, checking, _resolution,
      resolvedFrame, _seen, _resolvedStored, writing, _shape, coreSame, _adapted, _restart,
      _updatedSame, _restartSame, _nextSame, _notStuck, _classes, _resume⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.parked_singleton_removed_bucket_receipt
      holeKey fits admits graph templates false (fun _ => []) stop order workFuel 0 selected
      metadata updated caller memos.query before after checked restartCore next packet.safe.1.total actual
  have readSuccess : Success (getValue workFuel selected) before.core
      (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap workFuel selected oldHandle scs) readAfter true checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  have resolvedIncoming := EnumerationPendingReplacement.frame_incoming selected before.core resolved
    (readFrame.trans resolvedFrame) incoming
  have checkedIncoming := EnumerationPendingReplacement.setValue_clear_incoming selected root (some oldHandle)
    resolved checked resolvedIncoming writing
  have mass := SourcePruningEnumerationPrefixMass.parked_mass caller.checked.native.machine.heap
    workFuel workFuel selected oldHandle scs before.core readAfter checked packet.safe readSuccess checkSuccess
  rw [← coreSame] at checkedIncoming mass
  exact ⟨checkedIncoming, mass, Nat.le_trans mass originalMass⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem actual_narrowed_phase_admission
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (workFuel selected ceiling : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected))
    (originalMass : suspendedBound before.core ≤ ceiling)
    {checked actionCore callbackCore : Core} {value : Node}
    {heap : InternedConstructorTemplates.State Symbol Constraint}
    {action : EnumerateM Symbol Constraint Unit} {after : Cached}
    {reached : Caller width} {received : Queries} {updated : Metadata Typing}
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query =
        .narrowed checked (.done (value, some action) heap) reached received
          (some [.ok ((), actionCore)]) (some after) (some [.ok ((false, updated), callbackCore)]) none) :
    EnumerationReferences.IncomingAvoid selected after.core ∧
    suspendedBound after.core = suspendedBound before.core ∧ suspendedBound after.core ≤ ceiling ∧
    ∃ (oldHandle newHandle : Nat) (scs : List Suspended),
      before.core.values[selected]? = some (.unenumerated (some oldHandle) scs) ∧
      after.core.values[selected]? = some (.unenumerated (some newHandle) scs) ∧
      scs.length ≤ suspendedBound before.core ∧ scs.length ≤ ceiling := by
  obtain ⟨ready, incoming, _stored⟩ := SourcePruningEnumerationRestart.selected stop order metadata
    caller before selected packet.valid packet.safe chosen
  obtain ⟨oldHandle, newHandle, scs, oldValue, readAfter,
      reading, checking, _decoded, prepared, encoded, raw, _adapted, coreSame,
      _callbackSame, _updatedSame, _reachedSame, _receivedSame⟩ :=
    observed_success_stages holeKey fits admits graph templates stop order metadata updated
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller reached before after memos.query received
      checked actionCore callbackCore value heap action actual
  have readSuccess : Success (getValue workFuel selected) before.core
      (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap workFuel selected oldHandle scs) readAfter false checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  have execution : Success action checked () actionCore := by
    rw [Success, raw]
    exact List.mem_singleton_self _
  have narrowed := prepared_done_narrowed holeKey fits admits metadata workFuel workFuel selected
    oldHandle scs oldValue value caller.checked.native.machine.heap heap action prepared
  have nonempty := prepared_success_nonempty holeKey fits admits metadata workFuel workFuel selected
    oldHandle scs oldValue value caller.checked.native.machine.heap heap action checked actionCore prepared raw
  obtain ⟨finalIncoming, originalStored, finalStored⟩ := actual_narrowed_selected_bucket holeKey fits admits metadata
    workFuel selected oldHandle newHandle scs oldValue value caller.checked.native.machine.heap heap action
    before.core readAfter checked actionCore ready incoming readSuccess checkSuccess narrowed nonempty encoded prepared execution
  have mass := SourcePruningEnumerationPrefixMass.narrowed_mass holeKey fits admits metadata
    workFuel workFuel workFuel workFuel selected oldHandle newHandle scs oldValue value
    caller.checked.native.machine.heap heap action before.core readAfter checked actionCore packet.safe
    readSuccess checkSuccess narrowed nonempty encoded prepared execution
  have lengthBound : scs.length ≤ suspendedBound before.core := by
    obtain ⟨earlier, later, valuesSame⟩ := List.append_of_mem (List.mem_of_getElem? originalStored)
    unfold suspendedBound
    rw [valuesSame, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    dsimp only
    omega
  rw [← coreSame] at finalIncoming finalStored mass
  have ceilingBound : suspendedBound after.core ≤ ceiling := by
    rw [mass]
    exact originalMass
  exact ⟨finalIncoming, mass, ceilingBound, oldHandle, newHandle, scs,
    originalStored, finalStored, lengthBound, Nat.le_trans lengthBound originalMass⟩

/-- Actual continuing real prefixes retain incoming avoidance and the original bucket bounds. -/
theorem prefix_real_phase_admission_at_original_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (workFuel selected ceiling : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected))
    (originalMass : suspendedBound before.core ≤ ceiling) :
    let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query
    match observed with
    | .parked _ (some after) (some [.ok ((_updated, _next), _restartCore)]) =>
        EnumerationReferences.IncomingAvoid selected after.core ∧
        suspendedBound after.core ≤ suspendedBound before.core ∧
        suspendedBound after.core ≤ ceiling
    | .narrowed _ (.done (_value, some _action) _heap) _ _
        (some [.ok ((), _actionCore)]) (some after)
        (some [.ok ((false, _updated), _callbackCore)]) none =>
        EnumerationReferences.IncomingAvoid selected after.core ∧
        suspendedBound after.core = suspendedBound before.core ∧
        suspendedBound after.core ≤ ceiling ∧
        ∃ (oldHandle newHandle : Nat) (scs : List Suspended),
          before.core.values[selected]? = some (.unenumerated (some oldHandle) scs) ∧
          after.core.values[selected]? = some (.unenumerated (some newHandle) scs) ∧
          scs.length ≤ suspendedBound before.core ∧ scs.length ≤ ceiling
    | _ => True := by
  dsimp only
  split
  · apply actual_parked_phase_admission holeKey fits admits graph templates stop order metadata
      formulas solver inventory caller memos before packet workFuel selected ceiling chosen originalMass
    assumption
  · apply actual_narrowed_phase_admission holeKey fits admits graph templates stop order metadata
      formulas solver inventory caller memos before packet workFuel selected ceiling chosen originalMass
    assumption
  · trivial

end MicroCFTA.SourcePruningEnumerationSharedRecursive
