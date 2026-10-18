import MicroCFTA.SourceCurrentOuterUnionNormalHistory
import MicroCFTA.SourceCurrentOuterUntouchedProgress
import MicroCFTA.SourceEqualityNormalizationReceipt
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.OuterUnionNormalCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "UnionNormal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "readCaller" => SourceCurrentOuterActiveAncestry.caller
local notation "runPhase" => SourceCurrentOuterActiveAncestry.run
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private instance : DecidableEq Node := by classical exact inferInstance
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [],.top⟩
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def pair : Syntax Symbol Guard := .node [.mk ("pair",.top) own [leaf,leaf]]
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) own [leaf,leaf,pair]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def firstAllocation := SourceEqualityConstraintAllocation.construct own.equalities Cache.emptyState
private def first : SourceEqualityConstraintAllocation.Value := match firstAllocation.1 with
  | .ok value => value | _ => .contradiction
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities firstAllocation.2
private def inherited : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def checked : SourceEqualityNativeDemand.State 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
private theorem built_done : built = .done root heap := by cbv
private def original : Edge := (nodeEdges root)[0]?.getD (run (makeEdge ("root",.top) plain []) heap).1
private def caller := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty
  SourceCurrentEmptinessMemo.empty
private def request : EdgeRequest := ⟨inherited,original⟩
private def parent := edgeCall 8 4 0 16 12 16 64 16 16 256 0 request caller
private def parented : Edge := match parent with | .done value _ => value | _ => original
private def afterParent := parent.state
private theorem parent_done : parent = .done parented afterParent := by
  have tag : (match parent with | .done .. => true | _ => false) = true := by cbv
  cases found : parent <;> simp_all only [parented,afterParent,Outcome.state,Bool.false_eq_true]
private def entered := SourceCurrentAllocatedPartialGraph.prefixState afterParent parented inherited
private def source : Node := original.children[2]?.getD .empty
private def selected : Node := parented.children[2]?.getD .empty
private def row : Edge := (nodeEdges selected)[0]?.getD original
private def records : List SourceEqualityClassOrder.Record :=
  [(SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩]
private def next : Node := row.children[0]?.getD .empty
private def combinedValue : SourceEqualityConstraintAllocation.Value := first
private theorem combined : (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint
    inherited afterParent.checked.operations).1 = .ok (some combinedValue) := by cbv
private theorem live : combinedValue ≠ .contradiction := by cbv; intro impossible; cases impossible
private theorem selected_slot : parented.children[2]? = some selected := by cbv
private def prefixRun := walk 8 4 0 16 12 16 64 16 16 256 0 combinedValue 0
  (parented.children.take 2) entered
private def prefixOutputs : List Node := match prefixRun with | .done values _ => values | _ => []
private def prefixAfter := prefixRun.state
private theorem prefix_done : prefixRun = .done prefixOutputs prefixAfter := by
  have tag : (match prefixRun with | .done .. => true | _ => false) = true := by cbv
  cases found : prefixRun <;> simp_all only [prefixOutputs,prefixAfter,Outcome.state,Bool.false_eq_true]
private def rootRequest : NodeRequest := ⟨inherited,root⟩

private def firstPhase := SourceCurrentOuterCopiedWarmHit.Phase.rows 9 inherited [original] caller
private def lastPhase := SourceCurrentOuterCopiedWarmHit.Phase.node 5
  ⟨(SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).1,selected⟩
  (SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).2
private theorem reached : SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0 firstPhase lastPhase := by
  have rowStep : SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0
      (.rows 9 inherited [original] caller) (.descendants 8 inherited parented afterParent) :=
    .snoc (.refl _) (.rows_edge parent_done)
  have childStep := rowStep.snoc (SourceCurrentOuterExecutionAncestry.Step.descendants_children combined)
  have walkStep := childStep.snoc (SourceCurrentOuterExecutionAncestry.Step.children_walk live)
  have walked := SourceCurrentOuterUntouchedProgress.walk_prefix (fuel := 5) (slot := 2) prefix_done selected_slot
  exact walkStep.trans (by simpa only [Nat.reduceAdd,Nat.zero_add,entered,lastPhase] using walked)

/-- Actual completed siblings precede a normal unfinished child entry and its stopping state. -/
theorem actual_prefix :
    built = .done root heap ∧ parent = .done parented afterParent ∧
    prefixRun = .done prefixOutputs prefixAfter ∧
    SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0 firstPhase lastPhase ∧
    UnionNormal (readCaller lastPhase).checked.native.machine.heap ∧
    UnionNormal (runPhase 4 0 16 12 16 64 16 16 256 0 lastPhase).state.checked.native.machine.heap := by
  have normal := SourceCurrentOuterUnionNormalHistory.constructed expression (by rfl) reached
  exact ⟨built_done,parent_done,prefix_done,reached,normal⟩
end
end MicroCFTA.OuterUnionNormalCheck

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

#check @MicroCFTA.OuterUnionNormalCheck.actual_prefix
#print MicroCFTA.OuterUnionNormalCheck.actual_prefix
#print axioms MicroCFTA.OuterUnionNormalCheck.actual_prefix
