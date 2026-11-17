import MicroCFTA.SourcePruningEnumerationCausalHistoryInputInvariants
import MicroCFTA.SourcePruningEnumerationInvocationEventAuthenticity

namespace MicroCFTA.SourcePruningEnumerationJointCausalEventLedger
open SourcePruningEnumerationRealEagerCausalOutputHistory
open SourcePruningEnumerationCausalHistoryInputInvariants
open EnumerationValidity EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted continueWith)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow CapturedCallbackInvocationAt)
open SourcePruningEnumerationSharedChildVisitors (visitCapturedWith)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
universe u
variable {Typing Key : Type} {bits : Nat}
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "ActionRaw" => List (Except EnumerationState.Error (Unit × Core))
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [One joint causal ledger]
The mutual relations retain one qualified outer derivation and its actual cuts.
Each captured constructor uses one callback invocation and its exact receipt.
That invocation supplies the nested selected ledger at the same consumer index.
The event list contains only that row and its causal continuation.
Completed sibling prefixes retain native caller and query observations only.
They do not contribute sibling enum histories.

The relations have visible call, output and event-list indices.
They do not use a Prop proof as hidden-data identity.
A consumer must eliminate one joint derivation for all event witnesses.
The producer obtains the qualified history from initial Canonical and Total.
It has no future history, ledger, resource or model premise.

Opaque and shallow dispatch stay explicit atomic operation cuts.
The ledger does not assign semantic meaning to every primitive constraint.
It does not prove Suspended.Holds, TypeIn, native membership or one joint model.
-/

/-- Retain the actual arguments of each outer operation and nested event. -/
inductive Operation (Typing : Type) (width : Nat) where
  | parked (metadata : Metadata Typing) (uv : Nat) (caller : Caller width)
      (before : Cached) (queries : Queries) (checked : Core) (candidate : Cached)
      (updated : Metadata Typing) (next : Option Next) (core : Core)
  | selected (metadata : Metadata Typing) (uv : Nat) (caller : Caller width)
      (before : Cached) (queries : Queries) (checked : Core) (prepared : Prepared)
      (reached : Caller width) (saved : Queries) (action : Option ActionRaw) (candidate : Cached)
      (updated : Metadata Typing) (rightCore : Core)
  | prepare (uv : Nat) (caller : Caller width) (before : Cached) (target handle : Nat)
      (scs : List Suspended) (decoded : Node) (entered : Core) (value : Node)
      (heap : InternedConstructorTemplates.State Symbol Constraint)
  | opaque (target : Nat) (scs : List Suspended) (value : Node) (caller : Caller width)
      (before : Cached) (queries : Queries) (fragment : Fragment) (reached : Caller width)
      (saved : Queries) (finished : Cached)
  | finalize (target : Nat) (fragment : Fragment) (reached : Caller width)
      (before finished : Cached)
  | recordTypes (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
      (finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
  | nested (event : SourcePruningEnumerationInvocationEventLedger.Event width)

def CapturedEventLedgerAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
    (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
    (localIndex : Nat)
    (events : List (SourcePruningEnumerationInvocationEventLedger.Event (bits + 2))) : Prop
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
  SourcePruningEnumerationInvocationEventLedger.SelectedLedgerAt
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager consume
    scs edge caller before queries index output (.complete fragment reached saved beforeFinalize) localIndex [] events ∧
  (∀ event ∈ events, SourcePruningEnumerationInvocationEventLedger.AuthenticEvent event) ∧
  SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap workFuel target fragment beforeFinalize =
    some finished ∧
  ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
    (.inl fragment) finished.core) = [.ok ((false, updated), callbackCore)]

mutual
/-- Retain one complete qualified outer branch and its joint finite event list. -/
inductive JointOutputLedgerAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    Nat → Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
      Nat → Output (bits + 2) Typing → List (Operation Typing (bits + 2)) → Prop where
  | stopped (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (input : CanonicalTotal before.core) :
      JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before none 0 ⟨some metadata, before, caller, queries⟩ []
  | done (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (input : CanonicalTotal before.core) :
      JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before (some .done) 0 ⟨none, before, caller, queries⟩ []
  | parked
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller : Caller (bits + 2)} {queries : Queries} {before parkedCache : Cached}
      {checked core : Core} {next : Option Next} {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parkedCache) (some [.ok ((updated, next), core)]))
      (input : CanonicalTotal before.core) (check : CanonicalTotal checked)
      (candidate : CanonicalTotal parkedCache.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame core parkedCache).core)

      {tailEvents : List (Operation Typing (bits + 2))}
      (tailLedger : JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
        (EnumerationExpandableIndex.frame core parkedCache) next index output tailEvents) :
      JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (depth + 1) metadata caller queries before (some (.expand uv)) index output
        (.parked metadata uv caller before queries checked parkedCache updated next core :: tailEvents)
  | selected
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller reached : Caller (bits + 2)} {queries saved : Queries} {before after : Cached}
      {checked rightCore : Core} {prepared : Prepared} {action : Option ActionRaw}
      {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .narrowed checked prepared reached saved action (some after)
          (some [.ok ((false, updated), rightCore)]) none)
      (actionContinues : action ≠ some [])
      (input : CanonicalTotal before.core) (check : CanonicalTotal checked)
      (candidate : CanonicalTotal after.core)

      {preparedEvents : List (Operation Typing (bits + 2))}
      (preparedLedger : JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth updated uv reached saved after index output preparedEvents) :
      JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (depth + 1) metadata caller queries before (some (.expand uv)) index output
        (.selected metadata uv caller before queries checked prepared reached saved action after updated rightCore :: preparedEvents)

/-- Retain the same preparation, selected invocation and actual outer continuation. -/
inductive JointPreparedLedgerAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    Nat → Metadata Typing → Nat → Caller (bits + 2) → Queries → Cached →
      Nat → Output (bits + 2) Typing → List (Operation Typing (bits + 2)) → Prop where
  | opaque
      {depth uv target handle index : Nat} {metadata callbackMetadata : Metadata Typing}
      {caller completedCaller : Caller (bits + 2)} {queries saved : Queries}
      {before finished : Cached} {scs : List Suspended} {decoded value : Node}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {fragment : Fragment} {output : Output (bits + 2) Typing}
      (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
        ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
      (mode : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨
        (match value with | .node .. => False | _ => True))
      (completed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        workFuel workFuel workFuel workFuel workFuel target scs value
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (EnumerationExpandableIndex.frame entered before) queries =
        some (.complete fragment completedCaller saved finished))
      (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, callbackMetadata), callbackCore)])
      (input : CanonicalTotal before.core) (entry : CanonicalTotal entered)
      (bucket : ValidSuspended scs) (finalized : CanonicalTotal finished.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core)

      {tailEvents : List (Operation Typing (bits + 2))}
      (tailLedger : JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output tailEvents) :
      JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output
        (.prepare uv caller before target handle scs decoded entered value heap ::
          .opaque target scs value (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
            (EnumerationExpandableIndex.frame entered before) queries fragment completedCaller saved finished ::
          .recordTypes metadata uv fragment finished callbackMetadata callbackCore :: tailEvents)
  | captured
      {depth uv target handle index rowIndex tailIndex : Nat}
      {metadata callbackMetadata : Metadata Typing}
      {caller rowCaller completedCaller : Caller (bits + 2)} {queries rowQueries saved : Queries}
      {before beforeFinalize finished : Cached} {scs : List Suspended} {decoded : Node}
      {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List Edge}
      {ordinaryDepth : Nat} {free : List InternedBinderProtocol.Reference}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {attempted remaining : List Edge} {edge : Edge}
      {processed : List (SelectedEdge.Result (bits + 2))}
      {earlier later callbackEarlier callbackLater : List (Output (bits + 2) Typing)}
      {rowResult : Fold} {fragment : Fragment} {output : Output (bits + 2) Typing}
      (actual :
        let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
        let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel depth
        let hook := continueWith recur graph templates stop order workFuel metadata uv
        let rootBefore := EnumerationExpandableIndex.frame entered before
        let rootCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
        let visit := fun edge reached saved captured =>
          visitCapturedWith child hook workFuel target scs edge reached saved captured
        SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
          ([.ok ((target, handle, scs, decoded), entered)],
            some (.done (.node entry rows ordinaryDepth free) heap)) ∧
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
        edgesOf (.node entry rows ordinaryDepth free) = attempted ++ edge :: remaining ∧
        scan visit rootBefore attempted rootCaller queries = .complete processed earlier rowCaller rowQueries ∧
        visit edge rowCaller rowQueries rootBefore = rowResult ∧
        (outputs rowResult)[rowIndex]? = some output ∧
        index = earlier.length + rowIndex ∧
        outputs (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries) =
          earlier ++ outputs rowResult ++ later ∧
        CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
          workFuel depth uv target metadata scs edge rowCaller rowQueries rootBefore rowIndex output
          fragment completedCaller saved beforeFinalize finished callbackMetadata callbackCore
          callbackEarlier callbackLater tailIndex ∧
        outputs rowResult = callbackEarlier ++ emitted (recur callbackMetadata completedCaller saved
          (EnumerationExpandableIndex.frame callbackCore finished)
          (SourcePruningEnumerationRestart.decision stop order callbackMetadata
            (EnumerationExpandableIndex.frame callbackCore finished))) ++ callbackLater ∧
        rowIndex = callbackEarlier.length + tailIndex)
      (input : CanonicalTotal before.core) (entryFacts : CanonicalTotal entered)
      (bucket : ValidSuspended scs) (rowReturn : CanonicalTotal beforeFinalize.core)
      (finalized : CanonicalTotal finished.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core)

      {tailEvents : List (Operation Typing (bits + 2))}
      (tailLedger : JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output tailEvents)
      {nestedEvents : List (SourcePruningEnumerationInvocationEventLedger.Event (bits + 2))}
      (nestedLedger : CapturedEventLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel depth uv target metadata scs edge rowCaller rowQueries
        (EnumerationExpandableIndex.frame entered before) rowIndex output fragment completedCaller saved
        beforeFinalize finished callbackMetadata callbackCore tailIndex nestedEvents) :
      JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output
        (.prepare uv caller before target handle scs decoded entered (.node entry rows ordinaryDepth free) heap ::
          (nestedEvents.map Operation.nested ++
            (.finalize target fragment completedCaller beforeFinalize finished ::
              .recordTypes metadata uv fragment finished callbackMetadata callbackCore :: tailEvents)))
end

private theorem captured_invocation_event_ledger
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
    (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
    (earlier later : List (Output (bits + 2) Typing)) (localIndex : Nat)

    (invoked : CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output fragment reached saved
      beforeFinalize finished updated callbackCore earlier later localIndex) :
    ∃ events, CapturedEventLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output fragment reached saved
      beforeFinalize finished updated callbackCore localIndex events
 := by
  have receipt := invoked
  dsimp only [CapturedCallbackInvocationAt] at receipt
  obtain ⟨trace, _whole, _hit, _offset, finalized, recorded⟩ := receipt
  obtain ⟨events, ledger⟩ :=
    (SourcePruningEnumerationInvocationEventLedger.invocation_event_ledgers
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf).2.2
      .eager _ scs edge caller before queries index output
      (.complete fragment reached saved beforeFinalize) localIndex trace []
  have authentic :=
    (SourcePruningEnumerationInvocationEventLedger.invocation_ledger_events_authentic
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf).2.2
      .eager _ scs edge caller before queries index output
      (.complete fragment reached saved beforeFinalize) localIndex [] events ledger
  exact ⟨events, ledger, authentic, finalized, recorded⟩

theorem qualified_histories_joint_event_ledgers
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    (∀ (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (decision : Option Next)
      (index : Nat) (output : Output (bits + 2) Typing)
      (history : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before decision index output),
      QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history →
      ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before decision index output events) ∧
    (∀ (depth : Nat) (metadata : Metadata Typing) (uv : Nat) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
      (history : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output),
      QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history →
      ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output events)
 := by
  have stoppedCase (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (input : CanonicalTotal before.core) :
      ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before none 0 ⟨some metadata, before, caller, queries⟩ events := by
    exact ⟨[], JointOutputLedgerAt.stopped depth metadata caller queries before input⟩

  have doneCase (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (input : CanonicalTotal before.core) :
      ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before (some .done) 0 ⟨none, before, caller, queries⟩ events := by
    exact ⟨[], JointOutputLedgerAt.done depth metadata caller queries before input⟩

  have parkedCase
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller : Caller (bits + 2)} {queries : Queries} {before parkedCache : Cached}
      {checked core : Core} {next : Option Next} {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parkedCache) (some [.ok ((updated, next), core)]))
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
        (EnumerationExpandableIndex.frame core parkedCache) next index output)
      (input : CanonicalTotal before.core) (check : CanonicalTotal checked)
      (candidate : CanonicalTotal parkedCache.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame core parkedCache).core)
      (_qualifiedTail : QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail)
      (tailIH : ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
        (EnumerationExpandableIndex.frame core parkedCache) next index output events) :
      ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (depth + 1) metadata caller queries before (some (.expand uv)) index output events := by
    obtain ⟨_tailEvents, tailLedger⟩ := tailIH
    exact ⟨_, JointOutputLedgerAt.parked observed input check candidate callback tailLedger⟩

  have selectedCase
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller reached : Caller (bits + 2)} {queries saved : Queries} {before after : Cached}
      {checked rightCore : Core} {prepared : Prepared} {action : Option ActionRaw}
      {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .narrowed checked prepared reached saved action (some after)
          (some [.ok ((false, updated), rightCore)]) none)
      (actionContinues : action ≠ some [])
      (preparedHistory : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated uv reached saved after index output)
      (input : CanonicalTotal before.core) (check : CanonicalTotal checked)
      (candidate : CanonicalTotal after.core)
      (_qualifiedPreparation : QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel preparedHistory)
      (preparedIH : ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth updated uv reached saved after index output events) :
      ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (depth + 1) metadata caller queries before (some (.expand uv)) index output events := by
    obtain ⟨_preparedEvents, preparedLedger⟩ := preparedIH
    exact ⟨_, JointOutputLedgerAt.selected observed actionContinues input check candidate preparedLedger⟩

  have opaqueCase
      {depth uv target handle index : Nat} {metadata callbackMetadata : Metadata Typing}
      {caller completedCaller : Caller (bits + 2)} {queries saved : Queries}
      {before finished : Cached} {scs : List Suspended} {decoded value : Node}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {fragment : Fragment} {output : Output (bits + 2) Typing}
      (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
        ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
      (mode : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨
        (match value with | .node .. => False | _ => True))
      (completed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        workFuel workFuel workFuel workFuel workFuel target scs value
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (EnumerationExpandableIndex.frame entered before) queries =
        some (.complete fragment completedCaller saved finished))
      (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, callbackMetadata), callbackCore)])
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output)
      (input : CanonicalTotal before.core) (entry : CanonicalTotal entered)
      (bucket : ValidSuspended scs) (finalized : CanonicalTotal finished.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core)
      (_qualifiedTail : QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail)
      (tailIH : ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output events) :
      ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output events := by
    obtain ⟨_tailEvents, tailLedger⟩ := tailIH
    exact ⟨_, JointPreparedLedgerAt.opaque preparation (by cases value <;> exact mode)
      completed recorded input entry bucket finalized callback tailLedger⟩

  have capturedCase
      {depth uv target handle index rowIndex tailIndex : Nat}
      {metadata callbackMetadata : Metadata Typing}
      {caller rowCaller completedCaller : Caller (bits + 2)} {queries rowQueries saved : Queries}
      {before beforeFinalize finished : Cached} {scs : List Suspended} {decoded : Node}
      {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List Edge}
      {ordinaryDepth : Nat} {free : List InternedBinderProtocol.Reference}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {attempted remaining : List Edge} {edge : Edge}
      {processed : List (SelectedEdge.Result (bits + 2))}
      {earlier later callbackEarlier callbackLater : List (Output (bits + 2) Typing)}
      {rowResult : Fold} {fragment : Fragment} {output : Output (bits + 2) Typing}
      (actual :
        let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
        let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel depth
        let hook := continueWith recur graph templates stop order workFuel metadata uv
        let rootBefore := EnumerationExpandableIndex.frame entered before
        let rootCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
        let visit := fun edge reached saved captured =>
          visitCapturedWith child hook workFuel target scs edge reached saved captured
        SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
          ([.ok ((target, handle, scs, decoded), entered)],
            some (.done (.node entry rows ordinaryDepth free) heap)) ∧
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
        edgesOf (.node entry rows ordinaryDepth free) = attempted ++ edge :: remaining ∧
        scan visit rootBefore attempted rootCaller queries = .complete processed earlier rowCaller rowQueries ∧
        visit edge rowCaller rowQueries rootBefore = rowResult ∧
        (outputs rowResult)[rowIndex]? = some output ∧
        index = earlier.length + rowIndex ∧
        outputs (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries) =
          earlier ++ outputs rowResult ++ later ∧
        CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
          workFuel depth uv target metadata scs edge rowCaller rowQueries rootBefore rowIndex output
          fragment completedCaller saved beforeFinalize finished callbackMetadata callbackCore
          callbackEarlier callbackLater tailIndex ∧
        outputs rowResult = callbackEarlier ++ emitted (recur callbackMetadata completedCaller saved
          (EnumerationExpandableIndex.frame callbackCore finished)
          (SourcePruningEnumerationRestart.decision stop order callbackMetadata
            (EnumerationExpandableIndex.frame callbackCore finished))) ++ callbackLater ∧
        rowIndex = callbackEarlier.length + tailIndex)
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output)
      (input : CanonicalTotal before.core) (entryFacts : CanonicalTotal entered)
      (bucket : ValidSuspended scs) (rowReturn : CanonicalTotal beforeFinalize.core)
      (finalized : CanonicalTotal finished.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core)
      (_qualifiedTail : QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail)
      (tailIH : ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output events) :
      ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output events := by
    obtain ⟨_tailEvents, tailLedger⟩ := tailIH
    have receipt := actual
    dsimp only at receipt
    obtain ⟨_preparation, _nonterminal, _rowOrder, _completedPrefix, _rowRun, _rowHit,
      _rowOffset, _rowWhole, invoked, _callbackWhole, _callbackOffset⟩ := receipt
    obtain ⟨_nestedEvents, nestedLedger⟩ := captured_invocation_event_ledger
      holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel depth uv target metadata scs edge rowCaller rowQueries
      (EnumerationExpandableIndex.frame entered before) rowIndex output fragment completedCaller saved
      beforeFinalize finished callbackMetadata callbackCore callbackEarlier callbackLater tailIndex invoked
    exact ⟨_, JointPreparedLedgerAt.captured actual input entryFacts bucket rowReturn finalized callback
      tailLedger nestedLedger⟩

  constructor
  · intro depth metadata caller queries before decision index output history qualified
    exact QualifiedOutputHistoryAt.rec
      (motive_1 := fun {depth} {metadata} {caller} {queries} {before} {decision} {index} {output} _history _qualified =>
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth metadata caller queries before decision index output events)
      (motive_2 := fun {depth} {metadata} {uv} {caller} {queries} {before} {index} {output} _history _qualified =>
        ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth metadata uv caller queries before index output events)
      @stoppedCase @doneCase @parkedCase @selectedCase @opaqueCase @capturedCase qualified
  · intro depth metadata uv caller queries before index output history qualified
    exact QualifiedPreparedHistoryAt.rec
      (motive_1 := fun {depth} {metadata} {caller} {queries} {before} {decision} {index} {output} _history _qualified =>
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth metadata caller queries before decision index output events)
      (motive_2 := fun {depth} {metadata} {uv} {caller} {queries} {before} {index} {output} _history _qualified =>
        ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth metadata uv caller queries before index output events)
      @stoppedCase @doneCase @parkedCase @selectedCase @opaqueCase @capturedCase qualified

theorem resumeWithNarrow_real_eager_joint_event_ledger
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) (decision : Option Next)
    (index : Nat) (output : Output (bits + 2) Typing)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives)
    (observed : (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
      metadata caller queries before decision))[index]? = some output) :
    ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      recursiveDepth metadata caller queries before decision index output events
 := by
  obtain ⟨history, qualified⟩ :=
    resumeWithNarrow_real_eager_qualified_output_history holeKey fits admits graph templates
      checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision
      index output canonical total observed
  exact (qualified_histories_joint_event_ledgers holeKey fits admits graph templates
    checkEmpty edgesOf stop order workFuel).1
      recursiveDepth metadata caller queries before decision index output history qualified

end MicroCFTA.SourcePruningEnumerationJointCausalEventLedger
