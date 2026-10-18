import MicroCFTA.SourceCurrentOuterUntouchedProgress
import MicroCFTA.SourceCurrentOuterMergeHistory
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.OuterMergeHistoryCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
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
private theorem own_cached : SourceEqualityGuardReadback.Cached own.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready checked := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState firstAllocation.2 [own] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) own_cached (show firstAllocation = (.ok first,firstAllocation.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [own,plain] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      one SourceEqualityGuardReadback.empty_cached (show allocation = (.ok inherited,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [own,plain] := by
    intro guard member
    simp only [expression,pair,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,or_self] at member ⊢
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem checked_good : SourceCurrentNativeOperationHeap.Good checked :=
  ⟨⟨initial_ready.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,
    initial_ready.good.heap,initial_ready.good.operations,initial_ready.good.fields,initial_ready.semantic,initial_ready.costs⟩
private theorem source_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) heap := by
  simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) expression
private theorem probes : InternedFreshOrdinaryProbeHeap.Heap heap := by
  simpa only [built,heap] using InternedFreshOrdinaryProbeHeap.closed_heap expression
private def original : Edge := (nodeEdges root)[0]?.getD (run (makeEdge ("root",.top) plain []) heap).1
private theorem original_present : original ∈ nodeEdges root := by cbv; exact .head _
private theorem original_resident : EdgeResident heap original :=
  InternedEdgeResidency.resident_edges heap checked_good.semantic.ready.semantic.1.normal.facts.linked root source_available.resident
    original original_present
private def caller := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty
  SourceCurrentEmptinessMemo.empty
private def request : EdgeRequest := ⟨inherited,original⟩
private theorem initial_good : SourceCurrentOuterPrefixInvariants.Good caller :=
  SourceCurrentOuterPrefixInvariants.initial checked _ _ checked_good
    (SourceCurrentMemoMergeEffects.stored_empty _) probes
private theorem initial_request : SourceCurrentOuterPrefixInvariants.EdgeReady caller request := by
  refine ⟨?_,original_resident⟩
  exact (SourceEqualityConstraintFieldLookup.load_ready plain checked.operations.constraints
    checked_good.operations.constraints SourceEqualityGuardReadback.empty_cached
    ⟨inherited,.top⟩ (by cbv)).1
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
private theorem root_ready : SourceCurrentOuterPrefixInvariants.NodeReady caller rootRequest :=
  ⟨initial_request.1,source_available⟩
private def cold := nodeCall 16 4 0 16 12 16 64 16 16 256 0 rootRequest caller
private def coldValue : Node := match cold with | .done value _ => value | _ => .empty
private theorem cold_done : cold = .done coldValue cold.state := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases found : cold <;> simp_all only [coldValue,Outcome.state,Bool.false_eq_true]
private def warm := nodeCall 0 0 0 0 0 0 0 0 0 0 0 rootRequest cold.state
private theorem warm_done : warm = .done coldValue warm.state := by cbv
private def Raw := SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear
  (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula))
private theorem empty_raw : Raw (SourceCurrentMemoMergeGraph.empty : SourceCurrentMemoMergeGraph.Memo Symbol Guard) := by
  intro key entry impossible
  cases impossible
private theorem populated : (afterParent.merge (original.children[0]?.getD .empty).referenceOf).isSome = true := by cbv
private theorem checked_witness :
    built = .done root heap ∧
    cold = .done coldValue cold.state ∧ warm = .done coldValue warm.state ∧
    Raw cold.state.merge ∧ Raw warm.state.merge ∧
    (afterParent.merge (original.children[0]?.getD .empty).referenceOf).isSome = true ∧
    SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0
      (.rows 9 inherited [original] caller)
      (.node 5 ⟨(SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).1,selected⟩
        (SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).2) ∧
    Raw (SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).2.merge := by
  have firstRaw := SourceCurrentOuterMergeHistory.initial_node cold_done checked_good probes root_ready
  have physical := SourceCurrentOuterPrefixInvariants.node_done cold_done initial_good root_ready
  have finalReady : SourceCurrentOuterPrefixInvariants.NodeReady cold.state rootRequest :=
    ⟨root_ready.1.grows physical.2.1.operations.constraint_growth,
      physical.2.1.keeps.available _ root_ready.2⟩
  have lastRaw := SourceCurrentOuterMergeHistory.node_done warm_done physical.1 finalReady firstRaw
  have rowStep : SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0
      (.rows 9 inherited [original] caller) (.descendants 8 inherited parented afterParent) :=
    .snoc (.refl _) (.rows_edge parent_done)
  have childStep := rowStep.snoc (SourceCurrentOuterExecutionAncestry.Step.descendants_children combined)
  have walkStep := childStep.snoc (SourceCurrentOuterExecutionAncestry.Step.children_walk live)
  have walked := SourceCurrentOuterUntouchedProgress.walk_prefix prefix_done selected_slot
  have reached := walkStep.trans (by simpa only [Nat.zero_add] using walked)
  have inputs : SourceCurrentOuterPrefixInvariants.Inputs (.rows 9 inherited [original] caller) :=
    ⟨initial_request.1,fun edge member => by cases List.mem_singleton.mp member; exact original_resident⟩
  have prefixRaw := SourceCurrentOuterMergeHistory.reached reached initial_good inputs empty_raw
  exact ⟨built_done,cold_done,warm_done,firstRaw,lastRaw,populated,reached,prefixRaw⟩

/-- Actual cold and ready calls retain writers through an unfinished sibling prefix. -/
theorem cold_warm_prefix :
    built = .done root heap ∧
    cold = .done coldValue cold.state ∧ warm = .done coldValue warm.state ∧
    Raw cold.state.merge ∧ Raw warm.state.merge ∧
    (afterParent.merge (original.children[0]?.getD .empty).referenceOf).isSome = true ∧
    SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0
      (.rows 9 inherited [original] caller)
      (.node 5 ⟨(SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).1,selected⟩
        (SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).2) ∧
    Raw (SourceCurrentAllocatedPartialGraph.descend prefixAfter combinedValue 2).2.merge := checked_witness

end
end MicroCFTA.OuterMergeHistoryCheck
