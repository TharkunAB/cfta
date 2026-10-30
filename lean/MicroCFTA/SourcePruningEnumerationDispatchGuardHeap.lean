import MicroCFTA.SourcePruningEnumerationDispatch
import MicroCFTA.SourcePruningEnumerationNativeRequestInputs
import MicroCFTA.SourcePruningEnumerationNativeRequestGuardHeap
import MicroCFTA.SourceCurrentConjunctionAnnotationOutcome

/-!
# Guard annotations at every actual dispatch caller

Both operands derive from the original pending slots.
Actual native returns derive their own check fields.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual dispatch caller retains the same closed guard alphabet. -/
theorem dispatch_heap (alphabet : List Constraint)
    (closed : SourceCurrentNativeClosedGuardAlphabet.Closed alphabet)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller (bits + 2)) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap) :
    Heap (fun guard => guard ∈ alphabet)
      (dispatch checkEmpty nativeFuel p h beforeCaller before source target queries).2.1.checked.native.machine.heap := by
  by_cases same : source = target
  · simp only [dispatch, ite_eq_left same, Id.run]
    exact known
  · simp only [dispatch, ite_eq_right same, Id.run]
    cases sourceStored : before.values[source]? with
    | none => exact known
    | some sourceSlot =>
        cases sourceSlot with
        | eliminated => exact known
        | enumerated fragment =>
            dsimp only
            cases before.values[target]? <;> exact known
        | unenumerated sourceNode sourceScs =>
            dsimp only
            cases targetStored : before.values[target]? with
            | none => exact known
            | some targetSlot =>
                cases targetSlot with
                | eliminated | enumerated => exact known
                | unenumerated targetNode targetScs =>
                    dsimp only
                    cases sourceNode with
                    | none => exact known
                    | some sourceHandle =>
                        dsimp only
                        cases targetNode with
                        | none => exact known
                        | some targetHandle =>
                            dsimp only
                            obtain ⟨left, leftDecoded, leftAvailable, leftClosed⟩ :=
                              realized source sourceHandle sourceScs sourceStored
                            obtain ⟨right, rightDecoded, rightAvailable, rightClosed⟩ :=
                              realized target targetHandle targetScs targetStored
                            cases actualLeft : lookupNode beforeCaller.checked.native.machine.heap sourceHandle with
                            | none => exact known
                            | some observedLeft =>
                                dsimp only
                                have leftSame : left = observedLeft := Option.some.inj (leftDecoded.symm.trans actualLeft)
                                subst left
                                cases actualRight : lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                                | none => exact known
                                | some observedRight =>
                                    dsimp only
                                    have rightSame : right = observedRight := Option.some.inj (rightDecoded.symm.trans actualRight)
                                    subst right
                                    have inputs := SourcePruningEnumerationNativeRequestInputs.inputs_of_resources
                                      profile formulas solver inventory beforeCaller observedLeft observedRight memos
                                      initial fits room leftAvailable rightAvailable leftClosed rightClosed nativeFuel
                                    have retained := SourcePruningEnumerationNativeRequestGuardHeap.execute_heap
                                      alphabet closed nativeFuel observedLeft observedRight beforeCaller.checked
                                      initial.ready.good inputs known
                                    generalize nativeEq : SourceEqualityNativeDemand.execute nativeFuel
                                      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain
                                        observedLeft observedRight)) beforeCaller.checked = actual
                                    rw [nativeEq] at retained
                                    cases actual <;> try exact retained
                                    rename_i query queried
                                    obtain ⟨next, _source, _roots, receipt, post, _fitsAfter, _mass⟩ :=
                                      SourceCurrentAllocatedTargetQuery.raw_done_caller_resources profile nativeFuel
                                        formulas solver inventory beforeCaller queried observedLeft observedRight query memos
                                        initial fits room leftAvailable rightAvailable leftClosed rightClosed nativeEq
                                    have probes : InternedFreshOrdinaryProbeHeap.Heap queried.native.machine.heap :=
                                      post.context.probes
                                    have guarded : Heap (fun guard => guard ∈ alphabet)
                                        (afterQuery (EnumGuard := EnumGuard) checkEmpty p h source target sourceScs targetScs
                                          query queried beforeCaller queries).2.1.checked.native.machine.heap := by
                                      unfold afterQuery
                                      have phaseHeap : Heap (fun guard => guard ∈ alphabet)
                                          (if checkEmpty then
                                            SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                                          else (.done false queried beforeCaller.fourth, queries)).1.state.native.machine.heap := by
                                        cases checkEmpty with
                                        | false => exact retained
                                        | true =>
                                            exact SourceCurrentConjunctionAnnotationOutcome.enabled_check_heap
                                              (fun guard => guard ∈ alphabet) p h query queried beforeCaller.fourth queries
                                              receipt.effects.ready probes receipt.available retained
                                      generalize phaseEq : (if checkEmpty then
                                        SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                                        else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth,
                                          queries)) = phase
                                      have reached : Heap (fun guard => guard ∈ alphabet) phase.1.state.native.machine.heap := by
                                        rw [← phaseEq]
                                        exact phaseHeap
                                      obtain ⟨observed, afterQueries⟩ := phase
                                      cases observed <;> exact reached
                                    exact guarded

end MicroCFTA.SourcePruningEnumerationDispatch
