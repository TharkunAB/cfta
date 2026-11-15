import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.SourceCurrentUnionNormalNativePrograms
import MicroCFTA.SourceCurrentUnionNormalConjunction

/-!
# Union normality at every actual incoming endpoint

The native request and enabled check retain union normality.
Every bounded incoming result retains the actual returned caller heap.
No completed execution or future resource certificate is an input.
-/
namespace MicroCFTA
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos

namespace SourceCurrentAllocatedTargetQuery
variable {width : Nat}

/-- An actual completed target query preserves union normality. -/
theorem Step.unionNormal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
    {left right value : Node} {before after : Checked width}
    (actual : Step left right before value after)
    (normal : UnionNormal before.native.machine.heap) :
    UnionNormal after.native.machine.heap := by
  obtain ⟨fuel, completed⟩ := actual.done
  have retained := SourceCurrentUnionNormalNativePrograms.request fuel
    IntersectionEmptyDomain.emptyDomain left right before normal
  simpa only [completed, SourceEqualityNativeDemand.Outcome.state] using retained

/-- A target-query receipt retains union normality at its actual return. -/
theorem Receipt.unionNormal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {left right value : Node} {before after : Checked width}
    {memos : EndpointMemoGateTrace.Memos}
    (receipt : Receipt formulas solver inventory left right before value after memos)
    (normal : UnionNormal before.native.machine.heap) :
    UnionNormal after.native.machine.heap :=
  receipt.actual.unionNormal normal

end SourceCurrentAllocatedTargetQuery

namespace SourcePruningEnumerationEnabledEmpty
variable {width : Nat}

/-- Every enabled check retains union normality at its returned checked state. -/
theorem check_unionNormal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before : Checked width)
    (memo : SourceCurrentEmptinessMemo.Memo) (queries : Queries)
    (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (check p h query before memo queries).1.state.native.machine.heap := by
  unfold check
  dsimp only
  split
  · exact SourceCurrentUnionNormalConjunction.call p h
      SourceCurrentConjunctionTupleBudget.currentTupleBudget memo query before normal
  · exact normal

end SourcePruningEnumerationEnabledEmpty

namespace SourcePruningEnumerationIncomingNode
variable {EnumGuard : Type} {width : Nat}

/-- Every incoming result preserves union normality at its actual returned caller. -/
theorem run_unionNormal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (run checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries).2.1.checked.native.machine.heap := by
  unfold run
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
                  cases actualLookup : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap oldHandle with
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
                            SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                          else (.done false queried beforeCaller.fourth, queries)).1.state.native.machine.heap := by
                        cases checkEmpty with
                        | false => exact retained
                        | true =>
                            exact SourcePruningEnumerationEnabledEmpty.check_unionNormal
                              p h query queried beforeCaller.fourth queries retained
                      dsimp only
                      generalize phaseEq : (if checkEmpty then
                        SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth,
                          queries)) = phase
                      have reached : UnionNormal phase.1.state.native.machine.heap := by
                        rw [← phaseEq]
                        exact phaseNormal
                      obtain ⟨observed, afterQueries⟩ := phase
                      cases observed with
                      | done answer checkedAfter saved =>
                          dsimp only
                          cases SourcePruningEnumerationNodes.encodeNode (if answer then .empty else query) <;> exact reached
                      | failed fault checkedAfter saved => exact reached

end SourcePruningEnumerationIncomingNode
end MicroCFTA

#check @MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.unionNormal
#print axioms MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.unionNormal
#check @MicroCFTA.SourceCurrentAllocatedTargetQuery.Receipt.unionNormal
#print axioms MicroCFTA.SourceCurrentAllocatedTargetQuery.Receipt.unionNormal
#check @MicroCFTA.SourcePruningEnumerationEnabledEmpty.check_unionNormal
#print axioms MicroCFTA.SourcePruningEnumerationEnabledEmpty.check_unionNormal
#check @MicroCFTA.SourcePruningEnumerationIncomingNode.run_unionNormal
#print axioms MicroCFTA.SourcePruningEnumerationIncomingNode.run_unionNormal
