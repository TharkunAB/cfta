import MicroCFTA.SourcePruningEnumerationSharedDispatch
import MicroCFTA.SourceCurrentUnionNormalNativePrograms
import MicroCFTA.SourceCurrentSharedUnionNormalConjunction

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedDispatchUnionNormal
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem check_unionNormal
    (p h : Nat) (query : Node) (before : Checked width)
    (memo : SourceCurrentEmptinessMemo.Memo) (queries : Queries)
    (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (SourcePruningEnumerationSharedEnabledEmpty.check p h query before memo queries).1.state.native.machine.heap := by
  unfold SourcePruningEnumerationSharedEnabledEmpty.check
  dsimp only
  split
  · exact SourceCurrentSharedUnionNormalConjunction.call p h
      SourceCurrentConjunctionTupleBudget.currentTupleBudget memo query before normal
  · exact normal

/-- The actual shared check retains union normality at its returned caller on every outcome. -/
theorem afterQuery_unionNormal
    (checkEmpty : Bool) (p h : Nat) (source target : Nat)
    (sourceScs targetScs : List Suspended) (query : Node) (queried : Checked width)
    (beforeCaller : Caller width) (queries : Queries)
    (normal : UnionNormal queried.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedDispatch.afterQuery (EnumGuard := EnumGuard)
        checkEmpty p h source target sourceScs targetScs query queried beforeCaller queries).2.1.checked.native.machine.heap
 := by
  have retained : UnionNormal
      (if checkEmpty then
        SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
      else (SourcePruningEnumerationSharedEnabledEmpty.Outcome.skipped queried beforeCaller.fourth,
        queries)).1.state.native.machine.heap := by
    cases checkEmpty with
    | false => exact normal
    | true => exact check_unionNormal p h query queried beforeCaller.fourth queries normal
  unfold SourcePruningEnumerationSharedDispatch.afterQuery
  generalize phaseEq : (if checkEmpty then
    SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
  else (SourcePruningEnumerationSharedEnabledEmpty.Outcome.skipped queried beforeCaller.fourth,
    queries)) = phase
  rw [phaseEq] at retained
  obtain ⟨observed, saved⟩ := phase
  dsimp only at retained ⊢
  cases observed.completed <;> exact retained

/-- Every actual shared source-target dispatch retains its returned native heap normality. -/
theorem dispatch_unionNormal
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries).2.1.checked.native.machine.heap
 := by
  by_cases same : source = target
  · simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_left same, Id.run] using normal
  · cases sourceRead : before.values[source]? with
    | none =>
        simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceRead, Id.run] using normal
    | some sourceValue =>
        cases sourceValue with
        | eliminated =>
            simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceRead, Id.run] using normal
        | enumerated fragment =>
            cases targetRead : before.values[target]? <;>
              simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                sourceRead, targetRead, Id.run] using normal
        | unenumerated sourceNode sourceScs =>
            cases targetRead : before.values[target]? with
            | none =>
                simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                  sourceRead, targetRead, Id.run] using normal
            | some targetValue =>
                cases targetValue with
                | eliminated =>
                    simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                      sourceRead, targetRead, Id.run] using normal
                | enumerated fragment =>
                    simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                      sourceRead, targetRead, Id.run] using normal
                | unenumerated targetNode targetScs =>
                    cases sourceNode with
                    | none =>
                        simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                          sourceRead, targetRead, Id.run] using normal
                    | some sourceHandle =>
                        cases targetNode with
                        | none =>
                            simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                              sourceRead, targetRead, Id.run] using normal
                        | some targetHandle =>
                            cases leftRead : lookupNode beforeCaller.checked.native.machine.heap sourceHandle with
                            | none =>
                                simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                                  sourceRead, targetRead, leftRead, Id.run] using normal
                            | some left =>
                                cases rightRead : lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                                | none =>
                                    simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                                      sourceRead, targetRead, leftRead, rightRead, Id.run] using normal
                                | some right =>
                                    have retained := SourceCurrentUnionNormalNativePrograms.request nativeFuel
                                      IntersectionEmptyDomain.emptyDomain left right beforeCaller.checked normal
                                    generalize nativeEq : SourceEqualityNativeDemand.execute nativeFuel
                                      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain
                                        left right)) beforeCaller.checked = actual at retained
                                    cases actual <;> first
                                    | simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                                        sourceRead, targetRead, leftRead, rightRead, nativeEq, Id.run] using retained
                                    | rename_i query queried
                                      have later := afterQuery_unionNormal (EnumGuard := EnumGuard)
                                        checkEmpty p h source target sourceScs targetScs query queried
                                        beforeCaller queries retained
                                      simpa only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same,
                                        sourceRead, targetRead, leftRead, rightRead, nativeEq, Id.run] using later

end MicroCFTA.SourcePruningEnumerationSharedDispatchUnionNormal
