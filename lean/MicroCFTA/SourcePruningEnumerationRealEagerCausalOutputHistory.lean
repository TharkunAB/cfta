import MicroCFTA.SourcePruningEnumerationRealEagerCapturedCausalCallbackOrigin
import MicroCFTA.SourcePruningEnumerationSharedScanOutputBlocks
import MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot

namespace MicroCFTA.SourcePruningEnumerationRealEagerCausalOutputHistory
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

/- Note [Indexed outer eager causal history]
The relations record calls to the existing real eager worker.
Every recursive history uses the actual remaining outer depth.
The output index is supplied by the original caller.
The captured constructor keeps the completed scan prefix and native endpoint.
Every sibling row starts at the same captured enum cache.
The selected child invocation and callback block share one local index.
There is no constructor from arbitrary output membership or output equality.
These proof-only relations add no runtime worker.
They do not yet flatten all nested removed obligations or prove a joint model.
-/

mutual
/-- Record the actual outer calls that produce one supplied indexed output. -/
inductive OutputHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    Nat → Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
      Nat → Output (bits + 2) Typing → Prop where
  | stopped (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) :
      OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth metadata caller queries before none
        0 ⟨some metadata, before, caller, queries⟩
  | done (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) :
      OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth metadata caller queries before (some .done)
        0 ⟨none, before, caller, queries⟩
  | parked
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller : Caller (bits + 2)} {queries : Queries} {before parkedCache : Cached}
      {checked core : Core} {next : Option Next} {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parkedCache) (some [.ok ((updated, next), core)]))
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
        (EnumerationExpandableIndex.frame core parkedCache) next index output) :
      OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (depth + 1) metadata caller queries before
        (some (.expand uv)) index output
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
      (preparedHistory : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated uv reached saved after index output) :
      OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (depth + 1) metadata caller queries before
        (some (.expand uv)) index output

/-- Record the actual preparation and callback that supply an outer tail output. -/
inductive PreparedHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    Nat → Metadata Typing → Nat → Caller (bits + 2) → Queries → Cached →
      Nat → Output (bits + 2) Typing → Prop where
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
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output) :
      PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth metadata uv caller queries before index output
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
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output) :
      PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth metadata uv caller queries before index output
end

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem indexed_singleton {α : Type u} (value output : α) (index : Nat)
    (observed : ([value] : List α)[index]? = some output) : index = 0 ∧ output = value := by
  cases index with
  | zero =>
      change some value = some output at observed
      exact ⟨rfl, (Option.some.inj observed).symm⟩
  | succ index =>
      have impossible : (none : Option α) = some output := by simp at observed
      cases impossible

theorem resumeWithNarrow_real_eager_indexed_output_history_zero
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) (decision : Option Next)
    (index : Nat) (output : Output (bits + 2) Typing)
    (observed : (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel 0
      metadata caller queries before decision))[index]? = some output) :
    OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      0 metadata caller queries before decision index output
 := by
  cases decision with
  | none =>
      change ([⟨some metadata, before, caller, queries⟩] : List (Output (bits + 2) Typing))[index]? =
        some output at observed
      obtain ⟨sameIndex, sameOutput⟩ := indexed_singleton _ output index observed
      subst index output
      exact .stopped 0 metadata caller queries before
  | some decision =>
      cases decision with
      | done =>
          change ([⟨none, before, caller, queries⟩] : List (Output (bits + 2) Typing))[index]? =
            some output at observed
          obtain ⟨sameIndex, sameOutput⟩ := indexed_singleton _ output index observed
          subst index output
          exact .done 0 metadata caller queries before
      | stuck =>
          change ([] : List (Output (bits + 2) Typing))[index]? = some output at observed
          simp only [List.getElem?_nil] at observed
          cases observed
      | expand uv =>
          change ([] : List (Output (bits + 2) Typing))[index]? = some output at observed
          simp only [List.getElem?_nil] at observed
          cases observed

private theorem captured_preparation_history_of_depth_induction
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat)
    (smallerDepth : ∀ (nextMetadata : Metadata Typing) (nextCaller : Caller (bits + 2))
      (nextQueries : Queries) (nextBefore : Cached) (nextDecision : Option Next)
      (nextIndex : Nat) (nextOutput : Output (bits + 2) Typing),
      (emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel depth
        nextMetadata nextCaller nextQueries nextBefore nextDecision))[nextIndex]? = some nextOutput →
      OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth nextMetadata nextCaller nextQueries nextBefore nextDecision nextIndex nextOutput)
    (uv target handle : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (scs : List Suspended) (decoded : Node)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List Edge)
    (ordinaryDepth : Nat) (free : List InternedBinderProtocol.Reference)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)],
        some (.done (.node entry rows ordinaryDepth free) heap)))
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (index : Nat) (output : Output (bits + 2) Typing) :
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
    (outputs (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries))[index]? =
      some output →
    PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata uv caller queries before index output
 := by
  dsimp only
  intro observed
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
  obtain ⟨attempted, edge, remaining, rowCaller, rowQueries, processed, earlier, rowResult,
      rowIndex, later, rowOrder, prefixObserved, rowCall, rowHit, offset, whole⟩ :=
    SourcePruningEnumerationSharedScanOutputOrigins.scan_output_block_origin
      visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries index output observed
  have visitorHit : (outputs (visitCapturedWith child hook workFuel target scs
      edge rowCaller rowQueries rootBefore))[rowIndex]? = some output := by
    rw [← rowCall] at rowHit
    exact rowHit
  obtain ⟨fragment, completedCaller, saved, beforeFinalize, finished, callbackMetadata, callbackCore,
      callbackEarlier, callbackLater, tailIndex, _finalized, _recorded, callbackWhole, tailHit,
      callbackOffset, invoked⟩ :=
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.real_eager_captured_output_causal_callback_restart_origin
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth uv target
      metadata scs edge rowCaller rowQueries rootBefore rowIndex output visitorHit
  have tailHistory := smallerDepth callbackMetadata completedCaller saved
    (EnumerationExpandableIndex.frame callbackCore finished)
    (SourcePruningEnumerationRestart.decision stop order callbackMetadata
      (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output tailHit
  refine PreparedHistoryAt.captured
    (target := target) (handle := handle) (scs := scs) (decoded := decoded)
    (entry := entry) (rows := rows) (ordinaryDepth := ordinaryDepth) (free := free)
    (heap := heap) (entered := entered) (attempted := attempted) (remaining := remaining)
    (edge := edge) (rowCaller := rowCaller) (rowQueries := rowQueries) (processed := processed)
    (earlier := earlier) (later := later) (rowResult := rowResult) (rowIndex := rowIndex)
    (fragment := fragment) (completedCaller := completedCaller) (saved := saved)
    (beforeFinalize := beforeFinalize) (finished := finished) (callbackMetadata := callbackMetadata)
    (callbackCore := callbackCore) (callbackEarlier := callbackEarlier) (callbackLater := callbackLater)
    (tailIndex := tailIndex) ?_ tailHistory
  dsimp only
  refine ⟨preparation, nonterminal, rowOrder, prefixObserved, rowCall, ?_, offset, whole, invoked, ?_, callbackOffset⟩
  · rw [← rowCall]
    exact visitorHit
  · rw [← rowCall]
    exact callbackWhole

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem empty_index {α : Type u} (index : Nat) (output : α)
    (observed : ([] : List α)[index]? = some output) : False := by
  have impossible : (none : Option α) = some output := by simp at observed
  cases impossible

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem finish_outputs (uv : Nat) (folded : Fold) :
    emitted (SourcePruningEnumerationSharedPreparedRecursive.finish uv folded) = outputs folded := by
  cases folded <;> rfl

private theorem opaque_preparation_history_of_depth_induction
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat)
    (smallerDepth : ∀ (nextMetadata : Metadata Typing) (nextCaller : Caller (bits + 2))
      (nextQueries : Queries) (nextBefore : Cached) (nextDecision : Option Next)
      (nextIndex : Nat) (nextOutput : Output (bits + 2) Typing),
      (emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel depth
        nextMetadata nextCaller nextQueries nextBefore nextDecision))[nextIndex]? = some nextOutput →
      OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth nextMetadata nextCaller nextQueries nextBefore nextDecision nextIndex nextOutput)
    (uv target handle : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (scs : List Suspended) (decoded value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
    (mode : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨
      (match value with | .node .. => False | _ => True))
    (index : Nat) (output : Output (bits + 2) Typing) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
      (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel depth
    let hook := continueWith recur graph templates stop order workFuel metadata uv
    (outputs (SourcePruningEnumerationSharedReceiptContinuation.run hook
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
      (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        workFuel workFuel workFuel workFuel workFuel target scs value
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (EnumerationExpandableIndex.frame entered before) queries)))[index]? = some output →
    PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata uv caller queries before index output
 := by
  dsimp only
  intro observed
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
    graph templates checkEmpty edgesOf stop order workFuel depth
  generalize receiptRun : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
    workFuel workFuel workFuel workFuel workFuel target scs value
    (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
    (EnumerationExpandableIndex.frame entered before) queries = receipt at observed
  cases receipt with
  | none => exact False.elim (empty_index index output observed)
  | some receipt =>
      cases receipt with
      | unhandled => exact False.elim (empty_index index output observed)
      | rejected reached saved after => exact False.elim (empty_index index output observed)
      | finalizeStopped fragment reached saved after => exact False.elim (empty_index index output observed)
      | stopped completed observation candidate =>
          unfold SourcePruningEnumerationSharedReceiptContinuation.run at observed
          dsimp only at observed
          generalize _advanced : NativeContinuations.advance
            (.stopped completed observation candidate) = endpoint at observed
          cases endpoint with
          | none => exact False.elim (empty_index index output observed)
          | some endpoint =>
              obtain ⟨reached, saved⟩ := endpoint
              exact False.elim (empty_index index output observed)
      | complete fragment completedCaller saved finished =>
          have receiptOutputs : outputs (SourcePruningEnumerationSharedReceiptContinuation.run
              (continueWith recur graph templates stop order workFuel metadata uv)
              (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
              (some (.complete fragment completedCaller saved finished))) =
              emitted (continueWith recur graph templates stop order workFuel metadata uv
                fragment completedCaller saved finished) := by
            cases actual : continueWith recur graph templates stop order workFuel metadata uv
              fragment completedCaller saved finished <;>
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual, outputs, emitted]
          rw [receiptOutputs] at observed
          obtain ⟨callbackMetadata, callbackCore, recorded, _member⟩ :=
            SourcePruningEnumerationSharedPreparedRecursive.continueWith_output_restart
              recur graph templates stop order workFuel metadata uv fragment completedCaller saved finished
              output (List.mem_of_getElem? observed)
          have callbackEquation := SourcePruningEnumerationSharedPreparedRecursive.continue_recorded
            recur graph templates stop order workFuel metadata callbackMetadata uv fragment
            completedCaller saved finished callbackCore recorded
          rw [callbackEquation] at observed
          exact PreparedHistoryAt.opaque preparation (by cases value <;> exact mode) receiptRun recorded
            (smallerDepth callbackMetadata completedCaller saved
              (EnumerationExpandableIndex.frame callbackCore finished)
              (SourcePruningEnumerationRestart.decision stop order callbackMetadata
                (EnumerationExpandableIndex.frame callbackCore finished)) index output observed)

private theorem prepared_output_history_of_depth_induction
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat)
    (smallerDepth : ∀ (nextMetadata : Metadata Typing) (nextCaller : Caller (bits + 2))
      (nextQueries : Queries) (nextBefore : Cached) (nextDecision : Option Next)
      (nextIndex : Nat) (nextOutput : Output (bits + 2) Typing),
      (emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel depth
        nextMetadata nextCaller nextQueries nextBefore nextDecision))[nextIndex]? = some nextOutput →
      OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth nextMetadata nextCaller nextQueries nextBefore nextDecision nextIndex nextOutput)
    (metadata : Metadata Typing) (uv : Nat)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
      (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel depth
    let hook := continueWith recur graph templates stop order workFuel metadata uv
    let actual := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
      checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
    ∀ folded, actual.2 = some folded → ∀ (index : Nat) (output : Output (bits + 2) Typing),
      (outputs folded)[index]? = some output →
      PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output
 := by
  dsimp only
  unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
  dsimp only
  generalize preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before = observation
  intro folded observed index output hit
  obtain ⟨raw, native⟩ := observation
  cases native with
  | none => cases observed
  | some native =>
      cases native with
      | failed fault heap => cases observed
      | done value heap =>
          cases raw with
          | nil => cases observed
          | cons row rest =>
              cases row with
              | error fault => cases observed
              | ok pair =>
                  obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := pair
                  cases rest with
                  | cons second remaining => cases observed
                  | nil =>
                      dsimp only at observed
                      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
                      | true =>
                          rw [terminal] at observed
                          simp only [ite_true] at observed
                          cases Option.some.inj observed
                          exact opaque_preparation_history_of_depth_induction
                            holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
                            smallerDepth uv target handle metadata caller before queries scs decoded value heap entered
                            preparation (Or.inl terminal) index output hit
                      | false =>
                          rw [terminal] at observed
                          simp only [Bool.false_eq_true, ite_false] at observed
                          cases value with
                          | empty =>
                              cases Option.some.inj observed
                              exact opaque_preparation_history_of_depth_induction
                                holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
                                smallerDepth uv target handle metadata caller before queries scs decoded .empty heap entered
                                preparation (Or.inr True.intro) index output hit
                          | reference referenceName =>
                              cases Option.some.inj observed
                              exact opaque_preparation_history_of_depth_induction
                                holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
                                smallerDepth uv target handle metadata caller before queries scs decoded
                                (.reference referenceName) heap entered preparation (Or.inr True.intro) index output hit
                          | union entry members ordinaryDepth free =>
                              cases Option.some.inj observed
                              exact opaque_preparation_history_of_depth_induction
                                holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
                                smallerDepth uv target handle metadata caller before queries scs decoded
                                (.union entry members ordinaryDepth free) heap entered preparation
                                (Or.inr True.intro) index output hit
                          | mu entry body ordinaryDepth ordinary =>
                              cases Option.some.inj observed
                              exact opaque_preparation_history_of_depth_induction
                                holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
                                smallerDepth uv target handle metadata caller before queries scs decoded
                                (.mu entry body ordinaryDepth ordinary) heap entered preparation
                                (Or.inr True.intro) index output hit
                          | node entry rows ordinaryDepth free =>
                              cases Option.some.inj observed
                              exact captured_preparation_history_of_depth_induction
                                holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
                                smallerDepth uv target handle metadata caller before queries scs decoded
                                entry rows ordinaryDepth free heap entered preparation terminal index output hit

theorem resumeWithNarrow_real_eager_indexed_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) (decision : Option Next)
    (index : Nat) (output : Output (bits + 2) Typing)
    (observed : (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
      metadata caller queries before decision))[index]? = some output) :
    OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      recursiveDepth metadata caller queries before decision index output
 := by
  induction recursiveDepth generalizing metadata caller queries before decision index output with
  | zero =>
      exact resumeWithNarrow_real_eager_indexed_output_history_zero
        holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        metadata caller queries before decision index output observed
  | succ depth ih =>
      cases decision with
      | none =>
          change ([⟨some metadata, before, caller, queries⟩] : List (Output (bits + 2) Typing))[index]? =
            some output at observed
          obtain ⟨sameIndex, sameOutput⟩ := indexed_singleton _ output index observed
          subst index output
          exact .stopped (depth + 1) metadata caller queries before
      | some decision =>
          cases decision with
          | done =>
              change ([⟨none, before, caller, queries⟩] : List (Output (bits + 2) Typing))[index]? =
                some output at observed
              obtain ⟨sameIndex, sameOutput⟩ := indexed_singleton _ output index observed
              subst index output
              exact .done (depth + 1) metadata caller queries before
          | stuck => exact False.elim (empty_index index output observed)
          | expand uv =>
              rw [resumeWithNarrow] at observed
              dsimp only at observed
              generalize prefixObserved : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries = actual at observed
              cases actual with
              | stopped read checked => exact False.elim (empty_index index output observed)
              | parked checked candidate raw =>
                  cases candidate with
                  | none => exact False.elim (empty_index index output observed)
                  | some parkedCache =>
                      cases raw with
                      | none => exact False.elim (empty_index index output observed)
                      | some rows =>
                          cases rows with
                          | nil => exact False.elim (empty_index index output observed)
                          | cons row rest =>
                              cases row with
                              | error fault => exact False.elim (empty_index index output observed)
                              | ok pair =>
                                  obtain ⟨⟨updated, next⟩, core⟩ := pair
                                  cases rest with
                                  | cons second remaining => exact False.elim (empty_index index output observed)
                                  | nil =>
                                      exact OutputHistoryAt.parked prefixObserved
                                        (ih updated caller queries (EnumerationExpandableIndex.frame core parkedCache)
                                          next index output observed)
              | narrowed checked prepared reached saved action candidate right ordinary =>
                  rcases action with _ | (_ | ⟨actionHead, actionTail⟩)
                  all_goals first | exact False.elim (empty_index index output observed) | skip
                  all_goals
                    cases right with
                    | none => exact False.elim (empty_index index output observed)
                    | some rows =>
                        cases rows with
                        | nil => exact False.elim (empty_index index output observed)
                        | cons row rest =>
                            cases row with
                            | error fault => exact False.elim (empty_index index output observed)
                            | ok pair =>
                                obtain ⟨⟨pruned, updated⟩, core⟩ := pair
                                cases pruned with
                                | true =>
                                    cases rest with
                                    | nil => exact False.elim (empty_index index output observed)
                                    | cons second remaining => exact False.elim (empty_index index output observed)
                                | false =>
                                    cases rest with
                                    | cons second remaining => exact False.elim (empty_index index output observed)
                                    | nil =>
                                        cases candidate with
                                        | none => exact False.elim (empty_index index output observed)
                                        | some after =>
                                            cases ordinary with
                                            | some other => exact False.elim (empty_index index output observed)
                                            | none =>
                                                have good := prepared_output_history_of_depth_induction
                                                  holeKey fits admits graph templates checkEmpty edgesOf stop order
                                                  workFuel depth ih updated uv reached saved after
                                                dsimp only at good observed
                                                generalize dispatched : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
                                                  (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                  (continueWith
                                                    (resumeWithNarrow
                                                      (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                      (SourcePruningOuterNarrow.narrow holeKey fits admits)
                                                      graph templates checkEmpty edgesOf stop order workFuel depth)
                                                    graph templates stop order workFuel updated uv)
                                                  checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                                                  edgesOf reached after saved = executed at good observed
                                                obtain ⟨preparation, folded⟩ := executed
                                                dsimp only at good observed
                                                cases folded with
                                                | none => exact False.elim (empty_index index output observed)
                                                | some folded =>
                                                    have foldedHit : (outputs folded)[index]? = some output := by
                                                      rw [← finish_outputs uv folded]
                                                      exact observed
                                                    exact OutputHistoryAt.selected prefixObserved (by simp)
                                                      (good folded rfl index output foldedHit)

end MicroCFTA.SourcePruningEnumerationRealEagerCausalOutputHistory
