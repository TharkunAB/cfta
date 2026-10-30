import MicroCFTA.SourceCurrentAllocatedNativeStoredExecute
import MicroCFTA.SourceCurrentAllocatedNativeStoredEnabledEmpty
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourcePruningEnumerationDispatch

/-!
# Native structural certificates through the actual dispatcher

Both operands come from the actual current source and target slots.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredDispatch
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width bits : Nat} {EnumGuard : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual query continuation retains certificates at its own queried entry. -/
private theorem after_query_stored (checkEmpty : Bool) (p h source target : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (query : Node) (queried : Checked width) (beforeCaller : Caller width) (queries : Queries)
    (stored : Stored queried.native) :
    Stored (SourcePruningEnumerationDispatch.afterQuery (EnumGuard := EnumGuard) checkEmpty p h source target
      sourceScs targetScs query queried beforeCaller queries).2.1.checked.native := by
  have phaseStored : Stored (if checkEmpty then
      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
    else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth,
      queries)).1.state.native := by
    split
    · exact SourceCurrentAllocatedNativeStoredEnabledEmpty.check_stored
        p h query queried beforeCaller.fourth queries stored
    · exact stored
  dsimp only [SourcePruningEnumerationDispatch.afterQuery]
  generalize phaseEq : (if checkEmpty then
      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
    else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth,
      queries)) = phase at *
  rcases phase with ⟨observation, savedQueries⟩
  cases observation with
  | done answer checkedAfter saved =>
      change Stored checkedAfter.native
      exact phaseStored
  | failed fault checkedAfter saved =>
      change Stored checkedAfter.native
      exact phaseStored

/-- Every actual dispatch outcome retains the current native structural certificates. -/
theorem dispatch_native_stored (profile : Profile) (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller (bits + 2)) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries)
    (ready : SourceCurrentConjunctionClassScan.Ready beforeCaller.checked)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native) :
    Stored (SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries).2.1.checked.native := by
  dsimp only [SourcePruningEnumerationDispatch.dispatch, Id.run]
  split
  · change Stored beforeCaller.checked.native
    exact stored
  · cases sourceSlot : before.values[source]? with
    | none =>
        change Stored beforeCaller.checked.native
        exact stored
    | some sourceValue =>
        cases sourceValue with
        | eliminated =>
            change Stored beforeCaller.checked.native
            exact stored
        | enumerated =>
            cases targetSlot : before.values[target]? <;>
              change Stored beforeCaller.checked.native <;> exact stored
        | unenumerated sourceNode sourceScs =>
            cases targetSlot : before.values[target]? with
            | none =>
                change Stored beforeCaller.checked.native
                exact stored
            | some targetValue =>
                cases targetValue with
                | eliminated | enumerated =>
                    change Stored beforeCaller.checked.native
                    exact stored
                | unenumerated targetNode targetScs =>
                    cases sourceNode with
                    | none =>
                        change Stored beforeCaller.checked.native
                        exact stored
                    | some sourceHandle =>
                        cases targetNode with
                        | none =>
                            change Stored beforeCaller.checked.native
                            exact stored
                        | some targetHandle =>
                            dsimp only []
                            cases leftDecoded : lookupNode beforeCaller.checked.native.machine.heap sourceHandle with
                            | none =>
                                change Stored beforeCaller.checked.native
                                exact stored
                            | some left =>
                                cases rightDecoded : lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                                | none =>
                                    change Stored beforeCaller.checked.native
                                    exact stored
                                | some right =>
                                    dsimp only []
                                    obtain ⟨leftValue, leftFound, leftAvailable, leftClosed⟩ :=
                                      realized source sourceHandle sourceScs sourceSlot
                                    have leftSame := Option.some.inj (leftFound.symm.trans leftDecoded)
                                    subst leftValue
                                    obtain ⟨rightValue, rightFound, rightAvailable, rightClosed⟩ :=
                                      realized target targetHandle targetScs targetSlot
                                    have rightSame := Option.some.inj (rightFound.symm.trans rightDecoded)
                                    subst rightValue
                                    have actualRoom := fits.room room
                                    have rawStored := SourceCurrentAllocatedNativeStoredExecute.execute_stored bits
                                      beforeCaller.checked left right nativeFuel ready leftAvailable rightAvailable
                                      leftClosed rightClosed stored actualRoom.1 actualRoom.2.1 actualRoom.2.2
                                    cases actual : SourceEqualityNativeDemand.execute nativeFuel
                                        (.code (SourceRecursiveIntersectionCode.requestNode
                                          IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                                    | yielded remaining queried =>
                                        change Stored queried.native
                                        simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using rawStored
                                    | failed fault queried =>
                                        change Stored queried.native
                                        simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using rawStored
                                    | constraintError message queried =>
                                        change Stored queried.native
                                        simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using rawStored
                                    | blocked reason remaining queried =>
                                        change Stored queried.native
                                        simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using rawStored
                                    | done query queried =>
                                        have queriedStored : Stored queried.native := by
                                          simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using rawStored
                                        change Stored (SourcePruningEnumerationDispatch.afterQuery
                                          (EnumGuard := EnumGuard) checkEmpty p h source target sourceScs targetScs
                                          query queried beforeCaller queries).2.1.checked.native
                                        exact after_query_stored (EnumGuard := EnumGuard) checkEmpty p h source target
                                          sourceScs targetScs query queried beforeCaller queries queriedStored

end MicroCFTA.SourceCurrentAllocatedNativeStoredDispatch
