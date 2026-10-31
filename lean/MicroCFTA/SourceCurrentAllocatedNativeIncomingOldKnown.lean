import MicroCFTA.SourceCurrentAllocatedNativeIncomingKnown
import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback

/-! Old cache retention at actual native prefixes and successful incoming returns. -/
-- Physical check failure remains unproved.
set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
open SourcePruningEnumerationObservation (PendingRealized)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

private theorem execute_prefix {Output : Type}
    {length : Nat} {control : SourceEqualityNativeDemand.Control Output} {before final : Checked width} {value : Output}
    (trace : Trace length control before (.code (.pure value)) final) (fuel : Nat) :
    ∃ prefixFuel remaining current, Trace prefixFuel control before remaining current ∧
      (SourceEqualityNativeDemand.execute fuel control before).state = current := by
  induction fuel generalizing length control before with
  | zero => exact ⟨0, control, before, .refl _ _, rfl⟩
  | succ fuel ih =>
      cases trace with
      | refl => exact ⟨0, _, _, .refl _ _, rfl⟩
      | cons start entry next middle last result count inputs one tail =>
          obtain ⟨prefixFuel, remaining, current, checked, observed⟩ := ih tail
          refine ⟨prefixFuel + 1, remaining, current, Trace.cons _ _ _ _ _ _ prefixFuel inputs one checked, ?_⟩
          simpa only [SourceEqualityNativeDemand.execute, one] using observed

/-- Every actual bounded native query endpoint retains the old cache, including non-done endpoints. -/
theorem native_query_old_known (bits bound : Nat) (profile : Profile) (before : Checked (bits + 2))
    (cached : Cached) (left right : Node) (fuel : Nat)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile before) (room : Room bits profile)
    (known : KnownOrdinary bound before.native.machine.heap cached) :
    KnownOrdinary bound (SourceEqualityNativeDemand.execute fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before).state.native.machine.heap cached := by
  have bounds := fits.room room
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    ready.good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before
    ready.good ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable bounds.1 bounds.2.1 bounds.2.2).1
  obtain ⟨length, value, after, receipt, _⟩ := SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete
    (fun _ _ => true) before ready.good ready.idle left right leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed ranges
  obtain ⟨prefixFuel, remaining, current, tracePrefix, observed⟩ := execute_prefix receipt.trace fuel
  rw [observed]
  have physical := SourceCurrentAllocatedNativeSemanticTraceReadback.effects tracePrefix ready.good (fun _ => trivial)
  exact SourceSizedPrefixKnownOrdinaryHeap.keeps_known physical.2.2.1 known

open scoped Classical in
/-- Every exposed caller retains the old cache except an unproved failed physical check. -/
theorem run_old_known_except_failed_check (bits bound : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h uv : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos) (queries : SourceEndpointMemo.Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native) :
    let result := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h beforeCaller before.core uv incoming incomingScs queries
    Stored result.2.1.checked.native ∧
      match result.1 with
      | .error (.inr _) => True
      | _ => KnownOrdinary bound result.2.1.checked.native.machine.heap before := by
  classical
  constructor
  · exact SourceCurrentAllocatedNativeStoredIncoming.incoming_run_stored profile checkEmpty r n p h
      beforeCaller before.core uv incoming incomingScs queries initial.ready realized available closed fits room stored
  · cases reading : UnionFind.findRoot r before.core.representatives uv with
    | none => simpa only [SourcePruningEnumerationIncomingNode.run, reading] using known
    | some found =>
      simp only [SourcePruningEnumerationIncomingNode.run, reading]
      cases slot : before.core.values[found.representative]? with
      | none => exact known
      | some value =>
        cases value with
        | enumerated _fragment => exact known
        | eliminated => exact known
        | unenumerated oldNode oldScs =>
          dsimp only []
          cases oldNode with
          | none => cases SourcePruningEnumerationNodes.encodeNode incoming <;> exact known
          | some oldHandle =>
            obtain ⟨old, decoded, oldAvailable, oldClosed⟩ := realized found.representative oldHandle oldScs slot
            have bounds := fits.room room
            have nativeKnown := native_query_old_known bits bound profile beforeCaller.checked before incoming old n
              initial.ready available oldAvailable closed oldClosed fits room known
            simp only [decoded]
            cases actual : SourceEqualityNativeDemand.execute n
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                beforeCaller.checked with
            | yielded control current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | failed fault current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | constraintError message current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | blocked reason control current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | done query queried =>
              dsimp only []
              obtain ⟨next, _source, _roots, receipt, queryPost⟩ := SourceCurrentAllocatedTargetQuery.raw_done_caller_initial
                bits n formulas solver inventory beforeCaller queried incoming old query memos initial
                available oldAvailable closed oldClosed bounds.1 bounds.2.1 bounds.2.2 actual
              have queryKnown := SourceSizedPrefixKnownOrdinaryHeap.query_known receipt known
              generalize phaseEq : (if checkEmpty then
                SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth, queries)) = phase
              obtain ⟨outcome, _phaseQueries⟩ := phase
              cases outcome with
              | failed _fault _checkedAfter _saved => trivial
              | done answer checkedAfter saved =>
                have observedPhase := congrArg Prod.fst phaseEq
                have reached : KnownOrdinary bound checkedAfter.native.machine.heap before := by
                  cases checkEmpty with
                  | false =>
                    change SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth =
                      .done answer checkedAfter saved at observedPhase
                    cases observedPhase
                    exact queryKnown
                  | true =>
                    change (SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries).1 =
                      .done answer checkedAfter saved at observedPhase
                    dsimp only [SourcePruningEnumerationEnabledEmpty.check] at observedPhase
                    split at observedPhase
                    · obtain ⟨physicalAfter, physicalDone, same⟩ := SourceCurrentAllocatedConjunctionWorker.call_done observedPhase
                      subst checkedAfter
                      have call := SourceCurrentConjunctionWorkerCompletion.call_sound p h 1000 beforeCaller.fourth query
                        (SourceCurrentAllocatedNativeEffects.physical queried) answer physicalAfter saved physicalDone
                      obtain ⟨_final, _reads, post, _sound, _available, _unfolding, _queries⟩ :=
                        SourceCurrentAllocatedConjunctionCaller.actual formulas solver
                          (before := SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
                          call queryPost.context receipt.available
                      exact SourceSizedPrefixKnownOrdinaryHeap.post_known post queryKnown
                    · cases observedPhase
                      exact queryKnown
                cases answer <;> simp only [Bool.false_eq_true, ↓reduceIte]
                · cases SourcePruningEnumerationNodes.encodeNode query <;> exact reached
                · exact reached

end MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
