import MicroCFTA.SourcePruningEnumerationSharedIncomingNode
import MicroCFTA.SourceCurrentUnionNormalNativePrograms
import MicroCFTA.SourceCurrentSharedUnionNormalConjunction

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

private theorem check_unionNormal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
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

/-- Every actual shared incoming outcome retains union normality at its returned caller. -/
theorem run_unionNormal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
        beforeCaller before uv incoming incomingScs queries).2.1.checked.native.machine.heap := by
  unfold SourcePruningEnumerationSharedIncomingNode.run
  cases foundEq : UnionFind.findRoot representativeFuel before.representatives uv with
  | none => exact normal
  | some found =>
      dsimp only
      cases stored : before.values[found.representative]? with
      | none => exact normal
      | some oldSlot =>
          cases oldSlot with
          | eliminated | enumerated => exact normal
          | unenumerated oldNode oldScs =>
              dsimp only
              cases oldNode with
              | none => cases SourcePruningEnumerationNodes.encodeNode incoming <;> exact normal
              | some oldHandle =>
                  dsimp only
                  cases actualLookup : SourcePruningEnumerationNodes.lookupNode
                      beforeCaller.checked.native.machine.heap oldHandle with
                  | none => exact normal
                  | some old =>
                      dsimp only
                      have retained := SourceCurrentUnionNormalNativePrograms.request nativeFuel
                        IntersectionEmptyDomain.emptyDomain incoming old beforeCaller.checked normal
                      generalize nativeEq : SourceEqualityNativeDemand.execute nativeFuel
                        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain
                          incoming old)) beforeCaller.checked = actual
                      rw [nativeEq] at retained
                      cases actual <;> try exact retained
                      rename_i query queried
                      have phaseNormal : UnionNormal
                          (if checkEmpty then
                            SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
                          else (.skipped queried beforeCaller.fourth, queries)).1.state.native.machine.heap := by
                        cases checkEmpty with
                        | false => exact retained
                        | true => exact check_unionNormal p h query queried beforeCaller.fourth queries retained
                      dsimp only
                      generalize phaseEq : (if checkEmpty then
                        SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (SourcePruningEnumerationSharedEnabledEmpty.Outcome.skipped queried beforeCaller.fourth,
                          queries)) = phase
                      have reached : UnionNormal phase.1.state.native.machine.heap := by
                        rw [← phaseEq]
                        exact phaseNormal
                      obtain ⟨observed, afterQueries⟩ := phase
                      cases observed with
                      | skipped checkedAfter saved =>
                          dsimp only [SourcePruningEnumerationSharedEnabledEmpty.Outcome.completed]
                          cases SourcePruningEnumerationNodes.encodeNode query <;> exact reached
                      | performed checkedResult =>
                          cases checkedResult with
                          | done answer checkedAfter saved snapshot =>
                              dsimp only [SourcePruningEnumerationSharedEnabledEmpty.Outcome.completed]
                              cases SourcePruningEnumerationNodes.encodeNode
                                (if answer then .empty else query) <;> exact reached
                          | failed fault checkedAfter saved snapshot => exact reached

end MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal

#check MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal.run_unionNormal
#print axioms MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal.run_unionNormal
