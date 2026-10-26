import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.SourcePruningEnumerationIncomingObservedResources

/-!
# Original resources through actual incoming writes

The current realized slots derive native admission. Literal successful
incoming observations retain the numeric and guard forecast at their own
returned caller. Empty rejection retains its completed native effects.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol EnumGuard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "forecast" => SourcePruningEnumerationIncomingQuery.forecast
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Realized current slots and original numeric room derive the old native admission predicate. -/
theorem initial_ranges (profile : Profile) (beforeCaller : Caller (bits + 2)) (before : Core)
    (uv : Nat) (incoming : Node) (ready : SourceCurrentConjunctionClassScan.Ready beforeCaller.checked)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile) :
    match before.values[uv]? with
    | some (.unenumerated (some oldHandle) _) =>
        match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
        | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
            (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
            beforeCaller.checked
        | none => True
    | _ => True := by
  cases stored : before.values[uv]? with
  | none => trivial
  | some value =>
      cases value with
      | eliminated | enumerated => trivial
      | unenumerated oldNode oldScs =>
          cases oldNode with
          | none => trivial
          | some oldHandle =>
              cases decoded : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
              | none => trivial
              | some old =>
                  obtain ⟨value, found, resident, oldClosed⟩ := realized uv oldHandle oldScs stored
                  have same := Option.some.inj (found.symm.trans decoded)
                  subst value
                  have actualRoom := fits.room room
                  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original incoming
                    beforeCaller.checked.native.machine.heap ready.good.native.machine.1.coherent available closed
                  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original old
                    beforeCaller.checked.native.machine.heap ready.good.native.machine.1.coherent resident oldClosed
                  exact (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits beforeCaller.checked
                    ready.good ready.semantic incoming old leftOriginal rightOriginal available resident
                    actualRoom.1 actualRoom.2.1 actualRoom.2.2).1

/-- Literal successful incoming observations retain resources even when the raw branch rejects. -/
theorem observed_resources (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Core)
    (checkEmpty : Bool) (r n p h uv : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (memos : Memos) (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap)
    {result : Option (List (Except EnumerationState.Error (Unit × Core)))}
    {afterCaller : Caller (bits + 2)} {savedQueries : Queries} {read : Core}
    (observed : run checkEmpty r n p h beforeCaller before uv incoming incomingScs memos.query =
      (.ok result, afterCaller, savedQueries, read)) :
    Fits (forecast alphabet profile) afterCaller.checked ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) afterCaller.checked.native.machine.heap := by
  have unchanged : Fits (forecast alphabet profile) beforeCaller.checked ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) beforeCaller.checked.native.machine.heap := by
    refine ⟨fits.mono (SourcePruningEnumerationIncomingQuery.forecast_ge alphabet profile), ?_⟩
    intro key edge found
    exact SourceCurrentGeneratedQueryGuardResources.forecast_ge alphabet profile (known key edge found)
  rw [run] at observed
  cases foundEq : UnionFind.findRoot r before.representatives uv with
  | none =>
      simp only [foundEq] at observed
      have same := congrArg (fun output => output.2.1) observed
      rw [← same]
      exact unchanged
  | some found =>
      simp only [foundEq] at observed
      cases stored : before.values[found.representative]? with
      | none =>
          simp only [stored] at observed
          have same := congrArg (fun output => output.2.1) observed
          rw [← same]
          exact unchanged
      | some value =>
          cases value with
          | eliminated | enumerated =>
              simp only [stored] at observed
              have same := congrArg (fun output => output.2.1) observed
              rw [← same]
              exact unchanged
          | unenumerated oldNode oldScs =>
              simp only [stored] at observed
              cases oldNode with
              | none =>
                  cases encoded : encodeNode incoming <;> simp only [encoded] at observed <;>
                    have same := congrArg (fun output => output.2.1) observed <;>
                    rw [← same] <;> exact unchanged
              | some oldHandle =>
                  cases decoded : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
                  | none =>
                      simp only [decoded] at observed
                      have same := congrArg (fun output => output.2.1) observed
                      rw [← same]
                      exact unchanged
                  | some old =>
                      obtain ⟨value, found, resident, oldClosed⟩ := realized _ oldHandle oldScs stored
                      have same := Option.some.inj (found.symm.trans decoded)
                      subst value
                      simp only [decoded] at observed
                      cases native : SourceEqualityNativeDemand.execute n
                          (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                          beforeCaller.checked with
                      | yielded | failed | constraintError | blocked =>
                          simp only [native] at observed
                          cases observed
                      | done query queried =>
                          simp only [native] at observed
                          cases phase : (if checkEmpty then
                              SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth memos.query
                              else (.done false queried beforeCaller.fourth, memos.query)) with
                          | mk outcome queries =>
                              simp only [phase] at observed
                              cases outcome with
                              | failed => cases observed
                              | done answer checkedAfter saved =>
                                  have bounded := SourcePruningEnumerationIncomingQuery.raw_done_resources
                                    alphabet profile formulas solver inventory beforeCaller incoming old checkEmpty memos
                                    initial available resident closed oldClosed fits room known native phase
                                  cases encoded : encodeNode (if answer then .empty else query) <;>
                                    simp only [encoded, SourceCurrentAllocatedConjunctionWorker.Outcome.state,
                                      SourceCurrentAllocatedConjunctionWorker.Outcome.memo] at observed <;>
                                    have same := congrArg (fun output => output.2.1) observed <;>
                                    rw [← same] <;> exact bounded

end MicroCFTA.SourcePruningEnumerationIncomingNode
