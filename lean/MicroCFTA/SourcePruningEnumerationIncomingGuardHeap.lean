import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.SourcePruningEnumerationNativeRequestInputs
import MicroCFTA.SourcePruningEnumerationNativeRequestGuardHeap
import MicroCFTA.SourceCurrentConjunctionAnnotationOutcome

/-!
# Guard annotations at every actual incoming caller

Initial caller resources construct all native input plans.
The actual done branch derives its own coupled receipt and check fields.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
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

/-- Every returned caller retains the original closed guard alphabet, including raw failures. -/
theorem run_heap (alphabet : List Constraint)
    (closed : SourceCurrentNativeClosedGuardAlphabet.Closed alphabet)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller (bits + 2)) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (queries : Queries) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (incomingAvailable : Available beforeCaller.checked.native.machine.heap incoming)
    (incomingClosed : incoming.free = [])
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap) :
    Heap (fun guard => guard ∈ alphabet)
      (run checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries).2.1.checked.native.machine.heap := by
  unfold run
  cases foundEq : UnionFind.findRoot representativeFuel before.representatives uv with
  | none => exact known
  | some found =>
      dsimp only
      cases stored : before.values[found.representative]? with
      | none => exact known
      | some oldSlot =>
          cases oldSlot with
          | eliminated | enumerated => exact known
          | unenumerated oldNode oldScs =>
              dsimp only
              cases oldNode with
              | none => cases encodeNode incoming <;> exact known
              | some oldHandle =>
                  dsimp only
                  obtain ⟨old, decoded, available, oldClosed⟩ :=
                    realized found.representative oldHandle oldScs stored
                  cases actualLookup : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
                  | none => exact known
                  | some observedOld =>
                      dsimp only
                      have same : old = observedOld := Option.some.inj (decoded.symm.trans actualLookup)
                      subst old
                      have inputs := SourcePruningEnumerationNativeRequestInputs.inputs_of_resources
                        profile formulas solver inventory beforeCaller incoming observedOld memos initial fits room
                        incomingAvailable available incomingClosed oldClosed nativeFuel
                      have retained := SourcePruningEnumerationNativeRequestGuardHeap.execute_heap alphabet closed
                        nativeFuel incoming observedOld beforeCaller.checked initial.ready.good inputs known
                      generalize nativeEq : SourceEqualityNativeDemand.execute nativeFuel
                        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain
                          incoming observedOld)) beforeCaller.checked = actual
                      rw [nativeEq] at retained
                      cases actual <;> try exact retained
                      rename_i query queried
                      obtain ⟨next, _source, _roots, receipt, post, _fitsAfter, _mass⟩ :=
                        SourceCurrentAllocatedTargetQuery.raw_done_caller_resources profile nativeFuel
                          formulas solver inventory beforeCaller queried incoming observedOld query memos
                          initial fits room incomingAvailable available incomingClosed oldClosed nativeEq
                      have probes : InternedFreshOrdinaryProbeHeap.Heap queried.native.machine.heap :=
                        post.context.probes
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
                      dsimp only
                      generalize phaseEq : (if checkEmpty then
                        SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth,
                          queries)) = phase
                      have reached : Heap (fun guard => guard ∈ alphabet) phase.1.state.native.machine.heap := by
                        rw [← phaseEq]
                        exact phaseHeap
                      obtain ⟨observed, afterQueries⟩ := phase
                      cases observed with
                      | done answer checkedAfter saved =>
                          dsimp only
                          cases encodeNode (if answer then .empty else query) <;> exact reached
                      | failed fault checkedAfter saved => exact reached

end MicroCFTA.SourcePruningEnumerationIncomingNode
