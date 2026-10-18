import MicroCFTA.SourceCurrentOuterParentHeightGrowth
import MicroCFTA.SourceCurrentActualSharedLeafEvents
import MicroCFTA.SourceCurrentActualClassDispatch

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.SelectedProgressCheck
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq Node := by classical exact inferInstance
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [], .top⟩
private def equal : Guard := ⟨some [[[0],[1]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair",.top) equal [leaf,leaf]]
private def loop (name : String) : Syntax Symbol Guard := .binder false (.node [.mk (name,.top) plain [.var 0]])
private def wrapper (name : String) : Syntax Symbol Guard := .node [.mk ("wrap",.top) plain [.union [finite,loop name]]]
private def program : Syntax Symbol Guard := .node [.mk ("roots",.top) equal [wrapper "x",wrapper "y"]]
private def built := InternedFreshOrdinaryConstruction.build program [] empty
private def input : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def left : Node := (children input)[0]?.getD .empty
private def right : Node := (children input)[1]?.getD .empty
private def first := SourceEqualityConstraintAllocation.construct equal.equalities Cache.emptyState
private def second := SourceEqualityConstraintAllocation.construct plain.equalities first.2
private def equalValue : SourceEqualityConstraintAllocation.Value := match first.1 with | .ok value => value | _ => .contradiction
private def inherited : SourceEqualityConstraintAllocation.Value := match second.1 with | .ok value => value | _ => .contradiction
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 second.2 heap
private noncomputable def parent := SourceCurrentAllocatedParentWorker.edge 16 16 16 16 16 16 16 16 256 0
  ("roots",.top) equal inherited [left,right] before.checked before.fourth before.merge
private noncomputable def output : EdgeValue Symbol Guard := match parent with
  | .done value _ _ _ => value | _ => (run (makeEdge ("roots",.top) equal []) heap).1
private theorem computed :
    built = .done input heap ∧
    SourceCurrentAllocatedGateWorker.primary 16 [left,right] [[0],[1]] before.checked = .done false before.checked ∧
    parent = .done output parent.state parent.fourth parent.memo ∧
    MergedOrdinaryHeight.height left = 1 ∧ MergedOrdinaryHeight.height right = 1 ∧
    MergedOrdinaryHeight.edgeHeight output = 3 := by cbv
private theorem cached_equal : SourceEqualityGuardReadback.Cached equal.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [equal,plain] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState first.2 [equal] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached_equal (show first = (.ok equalValue,first.2) by cbv)
  exact SourceEqualityOriginalAllocationHistory.History.construct one SourceEqualityGuardReadback.empty_cached
    (show second = (.ok inherited,second.2) by cbv)
private theorem source_ready : SourceCurrentConjunctionClassScan.Ready before.checked ∧
    Available heap input ∧ input.free = [] ∧ SourceRecursiveIntersectionInputView.Original input := by
  have initial := SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid program
    (fun guard member => by
      simpa [program,wrapper,finite,leaf,loop,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        or_assoc,or_left_comm,or_comm] using member) input heap computed.1
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct _ initial.1.good.operations
  exact ⟨⟨⟨initial.1.good.native,initial.1.good.heap,allocated.1,initial.1.good.fields.grows allocated.2.1⟩,
    initial.1.semantic,initial.1.costs,initial.1.scopedCache,initial.1.idle⟩,initial.2⟩
mutual
private noncomputable def positive : Node → Nat
  | .node _ rows _ _ => rowPositive rows
  | _ => 0
termination_by value => sizeOf value
private noncomputable def childPositive : List Node → Nat
  | [] => 0
  | value :: rest => max (positive value) (childPositive rest)
termination_by values => sizeOf values
private noncomputable def rowPositive : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | .mk entry children :: rest =>
    max ((if SourceMemoGate.plain entry.key.constraint then 0 else 1) + childPositive children) (rowPositive rest)
termination_by rows => sizeOf rows
end
private theorem positive_computed : positive left = 0 ∧ positive right = 0 ∧
    childPositive output.children = 1 := by cbv
private theorem witness :
    ∃ (expression : Syntax Symbol Guard) (original : Node) (initial : Checked 8)
      (first second : Node) (returned : EdgeValue Symbol Guard) (final : Checked 8)
      (fourth : SourceCurrentEmptinessMemo.Memo) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
      (inherited : SourceEqualityConstraintAllocation.Value),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done original initial.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready initial ∧ Available initial.native.machine.heap original ∧
      original.free = [] ∧ SourceRecursiveIntersectionInputView.Original original ∧
      children original = [first,second] ∧
      SourceCurrentAllocatedGateWorker.primary 16 [first,second] [[0],[1]] initial = .done false initial ∧
      SourceCurrentAllocatedParentWorker.edge 16 16 16 16 16 16 16 16 256 0
        ("roots",.top) equal inherited [first,second] initial SourceCurrentEmptinessMemo.empty
        SourceCurrentMemoMergeGraph.empty = .done returned final fourth saved ∧
      returned.entry.key.constraint = equal ∧
      MergedOrdinaryHeight.height first = 1 ∧ MergedOrdinaryHeight.height second = 1 ∧
      MergedOrdinaryHeight.edgeHeight returned = 3 ∧
      positive first = 0 ∧ positive second = 0 ∧ childPositive returned.children = 1 := by
  rcases computed with ⟨built,gate,parentDone,leftHeight,rightHeight,resultHeight⟩
  exact ⟨program,input,before.checked,left,right,output,parent.state,parent.fourth,parent.memo,inherited,
    built,source_ready.1,source_ready.2.1,source_ready.2.2.1,source_ready.2.2.2,by cbv,gate,parentDone,
    by cbv,leftHeight,rightHeight,resultHeight,positive_computed⟩
/-- Accepted ordinary endpoints can expose finite constrained rows below explicit union boundaries. -/
theorem accepted_union_skeleton_growth :
    ∃ (expression : Syntax Symbol Guard) (original : Node) (initial : Checked 8)
      (first second : Node) (returned : EdgeValue Symbol Guard) (final : Checked 8)
      (fourth : SourceCurrentEmptinessMemo.Memo) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
      (inherited : SourceEqualityConstraintAllocation.Value),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done original initial.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready initial ∧ Available initial.native.machine.heap original ∧
      original.free = [] ∧ SourceRecursiveIntersectionInputView.Original original ∧
      children original = [first,second] ∧
      SourceCurrentAllocatedGateWorker.primary 16 [first,second] [[0],[1]] initial = .done false initial ∧
      SourceCurrentAllocatedParentWorker.edge 16 16 16 16 16 16 16 16 256 0
        ("roots",.top) equal inherited [first,second] initial SourceCurrentEmptinessMemo.empty
        SourceCurrentMemoMergeGraph.empty = .done returned final fourth saved ∧
      returned.entry.key.constraint = equal ∧
      MergedOrdinaryHeight.height first = 1 ∧ MergedOrdinaryHeight.height second = 1 ∧
      MergedOrdinaryHeight.edgeHeight returned = 3 ∧
      positive first = 0 ∧ positive second = 0 ∧ childPositive returned.children = 1 := witness
end MicroCFTA.SelectedProgressCheck
