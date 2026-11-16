import MicroCFTA.SourcePruningEnumerationSharedChildInvocationOrigins
import MicroCFTA.SourcePruningEnumerationSharedInvocationCombinators
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningEnumerationSharedOutputOrigin
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningOuterNarrow

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted)
open SourcePruningEnumerationSharedChildVisitors (visitSelected)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Captured callback invocation]
The selected producer supplies an invocation trace and its list decomposition
at the same terminal index. This receipt retains that index and those lists.
The finalizer and recordTypes use the exact arguments of the selected receipt.
-/
def CapturedCallbackInvocationAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
    (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
    (earlier later : List (Output (bits + 2) Typing)) (localIndex : Nat) : Prop
 :=
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
    graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
    graph templates stop order workFuel metadata uv
  let consume : SelectedEdge.Result (bits + 2) →
      NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
    fun receipt => match receipt with
    | .complete fragment reached saved after =>
        match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel target fragment after with
        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
            (some (.complete fragment reached saved finished))
        | none => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
            (some (.finalizeStopped fragment reached saved after))
    | other => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some other)
  SourcePruningEnumerationSharedInvocationTrace.SelectedInvocationAt
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager consume
    scs edge caller before queries index output (.complete fragment reached saved beforeFinalize) localIndex ∧
  outputs (visitSelected child consume scs edge caller before queries) =
    earlier ++ outputs (consume (.complete fragment reached saved beforeFinalize)) ++ later ∧
  (outputs (consume (.complete fragment reached saved beforeFinalize)))[localIndex]? = some output ∧
  index = earlier.length + localIndex ∧
  SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel target fragment beforeFinalize =
    some finished ∧
  ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
    (.inl fragment) finished.core) = [.ok ((false, updated), callbackCore)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem completed_callback_restart_origin
    (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
      NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel uv : Nat) (metadata : Metadata Typing)
    (caller reached : Caller (bits + 2)) (queries saved : Queries)
    (fragment : Fragments.Fragment Symbol) (finished : Cached) (index : Nat)
    (output : Output (bits + 2) Typing)
    (observed : (outputs (SourcePruningEnumerationSharedReceiptContinuation.run
      (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
        graph templates stop order workFuel metadata uv)
      caller queries (some (.complete fragment reached saved finished))))[index]? = some output) :
    ∃ (updated : Metadata Typing) (callbackCore : Core),
      ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, updated), callbackCore)] ∧
      let resumed := recur updated reached saved (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame callbackCore finished))
      outputs (SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
          graph templates stop order workFuel metadata uv)
        caller queries (some (.complete fragment reached saved finished))) = emitted resumed ∧
      (emitted resumed)[index]? = some output
 := by
  have receiptOutputs :
      outputs (SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
          graph templates stop order workFuel metadata uv)
        caller queries (some (.complete fragment reached saved finished))) =
      emitted (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
        graph templates stop order workFuel metadata uv fragment reached saved finished) := by
    cases actual : SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
      graph templates stop order workFuel metadata uv fragment reached saved finished <;>
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual, outputs, emitted]
  have callbackObserved := observed
  rw [receiptOutputs] at callbackObserved
  obtain ⟨updated, callbackCore, recorded, _restartMember⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.continueWith_output_restart recur
      graph templates stop order workFuel metadata uv fragment reached saved finished output
      (List.mem_of_getElem? callbackObserved)
  have callbackSame :
      SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
        workFuel metadata uv fragment reached saved finished =
      recur updated reached saved (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame callbackCore finished)) := by
    simp only [SourcePruningEnumerationSharedPreparedRecursive.continueWith, recorded]
  refine ⟨updated, callbackCore, recorded, ?_, ?_⟩
  · exact receiptOutputs.trans (congrArg emitted callbackSame)
  · rw [callbackSame] at callbackObserved
    exact callbackObserved



theorem real_eager_captured_output_causal_callback_restart_origin
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
      (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
      graph templates stop order workFuel metadata uv
    let actual := SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
      workFuel target scs edge caller queries before
    (outputs actual)[index]? = some output →
    ∃ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
        (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
        (earlier later : List (Output (bits + 2) Typing)) (localIndex : Nat),
      SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        workFuel target fragment beforeFinalize = some finished ∧
      ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, updated), callbackCore)] ∧
      let resumed := recur updated reached saved (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame callbackCore finished))
      outputs actual = earlier ++ emitted resumed ++ later ∧
      (emitted resumed)[localIndex]? = some output ∧ index = earlier.length + localIndex ∧
      CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel recursiveDepth uv target metadata scs edge caller queries before index output
        fragment reached saved beforeFinalize finished updated callbackCore earlier later localIndex
 := by
  dsimp only
  intro observedOutput
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
    graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
    graph templates stop order workFuel metadata uv
  let actual := SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
    workFuel target scs edge caller queries before
  let consume : SelectedEdge.Result (bits + 2) →
      NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
    fun receipt => match receipt with
    | .complete fragment reached saved after =>
        match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel target fragment after with
        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
            (some (.complete fragment reached saved finished))
        | none => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
            (some (.finalizeStopped fragment reached saved after))
    | other => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some other)
  have actualEq : actual = visitSelected child consume scs edge caller before queries :=
    SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts
      child hook workFuel target scs edge caller queries before
  change (outputs actual)[index]? = some output at observedOutput
  rw [actualEq] at observedOutput
  obtain ⟨receipt, localIndex, invocation, earlier, later, whole, hit, offset⟩ :=
    SourcePruningEnumerationSharedInvocationTrace.selected_invocation_origin
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager
      (SourcePruningEnumerationSharedInvocationTrace.eager_invocation_at
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      consume scs edge caller before queries index output observedOutput
  cases receipt with
  | complete fragment reached saved beforeFinalize =>
    cases finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        workFuel target fragment beforeFinalize with
    | none =>
      have consumed : consume (.complete fragment reached saved beforeFinalize) =
          .stopped [] [] (.edge (some (.finalizeStopped fragment reached saved beforeFinalize)) (reached, saved)) := by
        simpa only [consume, finalized] using
          SourcePruningEnumerationSharedReceiptContinuation.finalize_stopped
            hook caller reached queries saved fragment beforeFinalize
      have empty : outputs (consume (.complete fragment reached saved beforeFinalize)) = [] :=
        congrArg outputs consumed
      rw [empty] at hit
      cases hit
    | some finished =>
      have consumed : consume (.complete fragment reached saved beforeFinalize) =
          SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
            (some (.complete fragment reached saved finished)) := by
        simp only [consume, finalized]
      have receiptHit := hit
      rw [consumed] at receiptHit
      obtain ⟨updated, callbackCore, recorded, receiptOutputs, resumedHit⟩ :=
        completed_callback_restart_origin recur graph templates stop order workFuel uv metadata
          caller reached queries saved fragment finished localIndex output receiptHit
      have invoked : CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
          workFuel recursiveDepth uv target metadata scs edge caller queries before index output
          fragment reached saved beforeFinalize finished updated callbackCore earlier later localIndex := by
        exact ⟨invocation, whole, hit, offset, finalized, recorded⟩
      refine ⟨fragment, reached, saved, beforeFinalize, finished, updated, callbackCore,
        earlier, later, localIndex, finalized, recorded, ?_, resumedHit, offset, invoked⟩
      calc
        outputs actual = outputs (visitSelected child consume scs edge caller before queries) := congrArg outputs actualEq
        _ = earlier ++ outputs (consume (.complete fragment reached saved beforeFinalize)) ++ later := whole
        _ = earlier ++ emitted (recur updated reached saved (EnumerationExpandableIndex.frame callbackCore finished)
            (SourcePruningEnumerationRestart.decision stop order updated
              (EnumerationExpandableIndex.frame callbackCore finished))) ++ later := by
          rw [consumed, receiptOutputs]
  | unhandled =>
    change ([] : List (Output (bits + 2) Typing))[localIndex]? = some output at hit
    cases hit
  | rejected reached saved after =>
    change ([] : List (Output (bits + 2) Typing))[localIndex]? = some output at hit
    cases hit
  | finalizeStopped fragment reached saved after =>
    change ([] : List (Output (bits + 2) Typing))[localIndex]? = some output at hit
    cases hit
  | stopped completed observation candidate =>
    have empty : outputs (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
        (some (.stopped completed observation candidate))) = [] := by
      unfold SourcePruningEnumerationSharedReceiptContinuation.run
      dsimp only
      cases advanced : NativeContinuations.advance (.stopped completed observation candidate) with
      | none => rfl
      | some endpoint =>
        rcases endpoint with ⟨reached, saved⟩
        rfl
    change (outputs (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
      (some (.stopped completed observation candidate))))[localIndex]? = some output at hit
    rw [empty] at hit
    cases hit

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
