import MicroCFTA.SourceCurrentOuterPositionalDispatch
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.OuterPositionalDispatchCheck
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
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [pair]]
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
    rcases member with rfl | rfl | rfl <;> simp
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
  InternedEdgeResidency.resident_edges heap checked_good.semantic.ready.linked root source_available.resident
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
private def walked := walk 8 4 0 16 12 16 64 16 16 256 0 inherited 0 parented.children entered
private def outputs : List Node := match walked with | .done values _ => values | _ => []
private def afterWalk := walked.state
private theorem walk_done : walked = .done outputs afterWalk := by
  have tag : (match walked with | .done .. => true | _ => false) = true := by cbv
  cases found : walked <;> simp_all only [outputs,afterWalk,Outcome.state,Bool.false_eq_true]
private def source : Node := original.children[0]?.getD .empty
private def selected : Node := parented.children[0]?.getD .empty
private def row : Edge := (nodeEdges selected)[0]?.getD original
private def records : List SourceEqualityClassOrder.Record :=
  [(SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩]
private def next : Node := row.children[1]?.getD .empty
private theorem footprint : ∀ originals : List SourceEqualityClassOrder.Record,
    SourceEqualityPhysicalPayload.own request.value.entry.key.constraint = .ok (some originals) →
      ∀ record ∈ originals, SourceCurrentClassPositionalFootprints.Unselected record 0 1 := by
  have emptyOwn : SourceEqualityPhysicalPayload.own request.value.entry.key.constraint = .ok (some []) := by cbv
  intro originals same record member
  have only : originals = [] := Option.some.inj (Except.ok.inj (same.symm.trans emptyOwn))
  subst originals
  cases member
private theorem combined : (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint
    inherited afterParent.checked.operations).1 = .ok (some inherited) := by cbv
private theorem live : inherited ≠ .contradiction := by cbv; intro impossible; cases impossible
private theorem source_slot : original.children[0]? = some source := by cbv
private theorem selected_slot : parented.children[0]? = some selected := by cbv
private theorem selected_row : row ∈ nodeEdges selected := by cbv; exact .head _
private theorem positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) := by cbv
private theorem nonempty : records ≠ [] := by intro impossible; cases impossible
private theorem continuation : row.children[1]? = some next := by cbv

private theorem witness :
    built = .done root heap ∧ SourceCurrentOuterPrefixInvariants.Good caller ∧
    SourceCurrentOuterPositionalOrigins.Origins caller ∧
    parent = .done parented afterParent ∧ walked = .done outputs afterWalk ∧
    SourceCurrentPositionalOriginChain.Below 1 next source ∧
    InternedValueMass.value next < InternedValueMass.value source ∧
    ∃ (start finish : SourceCurrentAllocatedPartialState.State 8) (childFuel : Nat) (returned : Node),
      8 = childFuel + 0 + 1 ∧ outputs[0]? = some returned ∧
      nodeCall childFuel 4 0 16 12 16 64 16 16 256 0
        ⟨(SourceCurrentAllocatedPartialGraph.descend start inherited 0).1,selected⟩
        (SourceCurrentAllocatedPartialGraph.descend start inherited 0).2 = .done returned finish ∧
      SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0
        (.rows 9 inherited [original] caller)
        (.node childFuel ⟨(SourceCurrentAllocatedPartialGraph.descend start inherited 0).1,selected⟩
          (SourceCurrentAllocatedPartialGraph.descend start inherited 0).2) := by
  have origins := SourceCurrentOuterPositionalOrigins.initial checked SourceCurrentMemoMergeGraph.empty
    SourceCurrentEmptinessMemo.empty
  obtain ⟨_,_,below,smaller,start,finish,childFuel,returned,count,output,_earlier,called,_suffix,reached⟩ :=
    SourceCurrentOuterPositionalDispatch.edge_dispatch (rest := []) parent_done initial_good initial_request
      guards origins combined live walk_done footprint source_slot selected_slot selected_row positive nonempty continuation
  exact ⟨built_done,initial_good,origins,parent_done,walk_done,below,smaller,
    start,finish,childFuel,returned,count,output,called,reached⟩

/-- A constructed finite parent dispatches its positive pair child and retains a strictly smaller literal continuation. -/
theorem actual_dispatch :
    built = .done root heap ∧ SourceCurrentOuterPrefixInvariants.Good caller ∧
    SourceCurrentOuterPositionalOrigins.Origins caller ∧
    parent = .done parented afterParent ∧ walked = .done outputs afterWalk ∧
    SourceCurrentPositionalOriginChain.Below 1 next source ∧
    InternedValueMass.value next < InternedValueMass.value source ∧
    ∃ (start finish : SourceCurrentAllocatedPartialState.State 8) (childFuel : Nat) (returned : Node),
      8 = childFuel + 0 + 1 ∧ outputs[0]? = some returned ∧
      nodeCall childFuel 4 0 16 12 16 64 16 16 256 0
        ⟨(SourceCurrentAllocatedPartialGraph.descend start inherited 0).1,selected⟩
        (SourceCurrentAllocatedPartialGraph.descend start inherited 0).2 = .done returned finish ∧
      SourceCurrentOuterExecutionAncestry.Reached 4 0 16 12 16 64 16 16 256 0
        (.rows 9 inherited [original] caller)
        (.node childFuel ⟨(SourceCurrentAllocatedPartialGraph.descend start inherited 0).1,selected⟩
          (SourceCurrentAllocatedPartialGraph.descend start inherited 0).2) := witness

end
end MicroCFTA.OuterPositionalDispatchCheck
