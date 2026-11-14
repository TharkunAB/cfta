import MicroCFTA.SourcePruningEnumerationSelectedStepCompletion
import MicroCFTA.SourcePruningEnumerationRecursion

namespace MicroCFTA.SourceCurrentSelectedStepCheckedFrame
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable [DecidableEq Symbol] [DecidableEq Node]

attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Join the original selected-step result with its produced recursion frame. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos) (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ readFuel checkFuel nativeFuel representativeFuel indexFuel,
      ∀ er ec ei callbackFuel r n p h k,
        let observed := SourcePruningEnumerationSelectedStep.run holeKey fits admits graph templates
          checkEmpty edgesOf stop order metadata (readFuel + er) (checkFuel + ec) nativeFuel
          representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos.query
        SourcePruningEnumerationSelectedStep.Valid holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (readFuel + er) (checkFuel + ec) nativeFuel
          representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos observed ∧
        match observed with
        | .narrowed checked _ _ _ _ _ _ _ => Frame before.core checked
        | _ => True := by
  rcases SourcePruningEnumerationSelectedStep.complete holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory caller memos before preference uv
      roots initial safe pending selection realized paths counts flags with
    ⟨stepRead, stepCheck, nativeFuel, representativeFuel, indexFuel, valid⟩
  rcases SourcePruningEnumerationRecursion.selected_complete caller.checked.native.machine.heap
      before preference uv roots safe selection realized paths counts flags with
    ⟨selectedRead, handle, scs, value, readAfter, selectedCheck, repeated, after,
      _stored, lookup, _available, _closed, reads, _readFrame, checks, _ready, _paths,
      _realized, _counts, _flags, _incoming, _pending, notRepeated, _repeated⟩
  refine ⟨stepRead + selectedRead, stepCheck + selectedCheck, nativeFuel, representativeFuel,
    indexFuel, ?_⟩
  intro er ec ei callbackFuel r n p h k
  constructor
  · simpa only [Nat.add_assoc] using
      valid (selectedRead + er) (selectedCheck + ec) ei callbackFuel r n p h k
  · have read : ExceptT.run (getValue ((stepRead + selectedRead) + er) uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)] := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reads (stepRead + er)
    have check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap ((stepCheck + selectedCheck) + ec) uv handle scs
        readAfter) = [.ok (repeated, after.core)] := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using checks (stepCheck + ec)
    have prefixFrame :
        match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
          stop order metadata ((stepRead + selectedRead) + er) ((stepCheck + selectedCheck) + ec)
          nativeFuel representativeFuel (indexFuel + ei) callbackFuel uv caller before memos.query with
        | .narrowed checked _ _ _ _ _ _ _ => Frame before.core checked
        | _ => True := by
      generalize hp : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata ((stepRead + selectedRead) + er) ((stepCheck + selectedCheck) + ec)
        nativeFuel representativeFuel (indexFuel + ei) callbackFuel uv caller before memos.query = observed
      cases observed with
      | stopped raw checked => trivial
      | parked checked candidate raw => trivial
      | narrowed checked prepared reached queries action candidate right ordinary =>
        cases repeated with
        | false =>
          have frame := (notRepeated rfl).1
          simp only [SourcePruningEnumerationSelectedStep.runPrefix,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, read, check, lookup] at hp
          repeat first
            | split at hp
            | (injection hp with checked_eq
               cases checked_eq
               exact frame)
        | true =>
          simp only [SourcePruningEnumerationSelectedStep.runPrefix,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, read, check] at hp
          all_goals cases hp
    generalize hout : SourcePruningEnumerationSelectedStep.run holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata ((stepRead + selectedRead) + er)
      ((stepCheck + selectedCheck) + ec) nativeFuel representativeFuel (indexFuel + ei)
      callbackFuel r n p h k uv caller before memos.query = observed
    cases observed with
    | stopped raw checked => trivial
    | parked checked candidate raw => trivial
    | narrowed checked prepared reached queries action candidate right ordinary =>
      change Frame before.core checked
      unfold SourcePruningEnumerationSelectedStep.run at hout
      generalize hp : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata ((stepRead + selectedRead) + er) ((stepCheck + selectedCheck) + ec)
        nativeFuel representativeFuel (indexFuel + ei) callbackFuel uv caller before memos.query = observedPrefix
        at hout prefixFrame
      cases observedPrefix with
      | stopped raw checked =>
        simp only [SourcePruningEnumerationSelectedStep.finish] at hout
        all_goals cases hout
      | parked checked candidate raw =>
        simp only [SourcePruningEnumerationSelectedStep.finish] at hout
        all_goals cases hout
      | narrowed prefixChecked prefixPrepared prefixCaller prefixQueries prefixAction prefixCandidate
          prefixRight prefixOrdinary =>
        change Frame before.core prefixChecked at prefixFrame
        simp only [SourcePruningEnumerationSelectedStep.finish] at hout
        split at hout
        · rename_i matched
          injection matched with prefix_checked_eq
          injection hout with result_checked_eq
          rw [← result_checked_eq, ← prefix_checked_eq]
          exact prefixFrame
        · injection hout with result_checked_eq
          rw [← result_checked_eq]
          exact prefixFrame

end MicroCFTA.SourceCurrentSelectedStepCheckedFrame
