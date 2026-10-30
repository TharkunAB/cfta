import MicroCFTA.SourceCurrentAllocatedNativeStoredExecute
import MicroCFTA.SourceCurrentAllocatedNativeStoredEnabledEmpty
import MicroCFTA.SourcePruningEnumerationIncomingNodeResources

/-!
# Native structural certificates through actual incoming writes

All entry properties concern the current caller and enumeration state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredIncoming
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {bits : Nat} {EnumGuard : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual incoming outcome retains the current native structural certificates. -/
theorem incoming_run_stored (profile : Profile) (checkEmpty : Bool)
    (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller (bits + 2)) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries)
    (ready : SourceCurrentConjunctionClassScan.Ready beforeCaller.checked)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native) :
    Stored (SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
      beforeCaller before uv incoming incomingScs queries).2.1.checked.native := by
  dsimp only [SourcePruningEnumerationIncomingNode.run]
  cases root : UnionFind.findRoot representativeFuel before.representatives uv with
  | none => exact stored
  | some found =>
      dsimp only []
      cases slot : before.values[found.representative]? with
      | none => exact stored
      | some value =>
          cases value with
          | eliminated | enumerated => exact stored
          | unenumerated oldNode oldScs =>
              dsimp only []
              cases oldNode with
              | none =>
                  cases encoded : encodeNode incoming <;> exact stored
              | some oldHandle =>
                  dsimp only []
                  cases decoded : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
                  | none => exact stored
                  | some old =>
                      dsimp only []
                      obtain ⟨value, foundValue, resident, oldClosed⟩ :=
                        realized found.representative oldHandle oldScs slot
                      have same := Option.some.inj (foundValue.symm.trans decoded)
                      subst value
                      have actualRoom := fits.room room
                      have rawStored := SourceCurrentAllocatedNativeStoredExecute.execute_stored bits
                        beforeCaller.checked incoming old nativeFuel ready available resident closed oldClosed stored
                        actualRoom.1 actualRoom.2.1 actualRoom.2.2
                      cases actual : SourceEqualityNativeDemand.execute nativeFuel
                          (.code (SourceRecursiveIntersectionCode.requestNode
                            IntersectionEmptyDomain.emptyDomain incoming old)) beforeCaller.checked with
                      | yielded remaining queried =>
                          simpa only [actual, SourceEqualityNativeDemand.Outcome.state,
                            SourceCurrentAllocatedPartialState.advance] using rawStored
                      | failed fault queried =>
                          simpa only [actual, SourceEqualityNativeDemand.Outcome.state,
                            SourceCurrentAllocatedPartialState.advance] using rawStored
                      | constraintError message queried =>
                          simpa only [actual, SourceEqualityNativeDemand.Outcome.state,
                            SourceCurrentAllocatedPartialState.advance] using rawStored
                      | blocked reason remaining queried =>
                          simpa only [actual, SourceEqualityNativeDemand.Outcome.state,
                            SourceCurrentAllocatedPartialState.advance] using rawStored
                      | done query queried =>
                          dsimp only []
                          have queriedStored : Stored queried.native := by
                            simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using rawStored
                          have phaseStored : Stored (if checkEmpty then
                              SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                            else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth,
                              queries)).1.state.native := by
                            split
                            · exact SourceCurrentAllocatedNativeStoredEnabledEmpty.check_stored
                                p h query queried beforeCaller.fourth queries queriedStored
                            · exact queriedStored
                          generalize phaseEq : (if checkEmpty then
                              SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                            else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth,
                              queries)) = phase at *
                          rcases phase with ⟨observation, savedQueries⟩
                          dsimp only [] at phaseStored ⊢
                          cases observation with
                          | failed fault checkedAfter saved => exact phaseStored
                          | done answer checkedAfter saved =>
                              dsimp only []
                              cases encoded : encodeNode (if answer then .empty else query) <;> exact phaseStored

end MicroCFTA.SourceCurrentAllocatedNativeStoredIncoming
