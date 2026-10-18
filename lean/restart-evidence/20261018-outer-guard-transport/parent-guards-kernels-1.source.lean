import MicroCFTA.SourceCurrentParentGuardHeapReturns
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 50000000

namespace MicroCFTA.ParentGuardsCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
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
private instance : DecidableEq Node := by classical exact inferInstance
private def plain : Guard := ⟨some [],.top⟩
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def leftPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("base",.top) plain [],.mk ("loop",.top) plain [.var 0],.mk ("left",.top) plain []])
private def rightPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("base",.top) plain [],.mk ("loop",.top) plain [.var 0],.mk ("right",.top) plain []])
private def expression : Syntax Symbol Guard := .node [.mk ("pair",.top) own [leftPlan,rightPlan]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Node := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def values := children value
private def firstAllocation := SourceEqualityConstraintAllocation.construct own.equalities Cache.emptyState
private def first : SourceEqualityConstraintAllocation.Value := match firstAllocation.1 with
  | .ok result => result | _ => .contradiction
private def secondAllocation := SourceEqualityConstraintAllocation.construct plain.equalities firstAllocation.2
private def inherited : SourceEqualityConstraintAllocation.Value := match secondAllocation.1 with
  | .ok result => result | _ => .contradiction
private def before : Checked 10 :=
  ⟨initial 10 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial secondAllocation.2⟩
private def annotation (guard : Guard) : Prop := guard = own
private def call := SourceCurrentAllocatedParentWorker.edge 32 32 32 32 32 32 32 32 64 8
  ("pair",.top) own inherited values before SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty
private def result := match call with | .done edge _ _ _ => edge
  | .failed .. => (run (makeEdge ("pair",.top) own []) heap).1

private theorem constructed : built = .done value heap := by cbv
private theorem own_cached : SourceEqualityGuardReadback.Cached own.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState secondAllocation.2 [own,plain] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState firstAllocation.2 [own] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) own_cached (show firstAllocation = (.ok first,firstAllocation.2) by cbv)
  simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    one SourceEqualityGuardReadback.empty_cached (show secondAllocation = (.ok inherited,secondAllocation.2) by cbv)
private theorem initial : SourceCurrentConjunctionClassScan.Ready before ∧ Available heap value := by
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [own,plain] := by
    intro guard member
    simp only [expression,leftPlan,rightPlan,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.nil_append,List.append_nil,or_false,or_self] at member ⊢
    tauto
  have entry := SourceCurrentConjunctionClassHistoryEntry.constructed 10 history Cache.empty_valid expression covered value heap constructed
  exact ⟨entry.1,entry.2.1⟩
private theorem good : SourceCurrentNativeOperationHeap.Good before :=
  ⟨initial.1.good.native,initial.1.good.heap,initial.1.good.operations,initial.1.good.fields,initial.1.semantic,initial.1.costs⟩
private theorem available : InternedNestedProvenance.Values heap values := initial.2.children
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap annotation expression
private theorem root_field : SourceCurrentConjunctionEquality.FieldAvailable before.operations own := by
  let edge := (nodeEdges value).headD (run (makeEdge ("pair",.top) own []) heap).1
  have member : edge ∈ nodeEdges value := by cbv; exact .head _
  have resident := InternedEdgeResidency.resident_edges heap good.native.machine.1.linked value initial.2.resident edge member
  have field := good.fields edge.entry.key edge resident
  have same : edge.entry.key.constraint = own := by cbv
  exact same ▸ field
private theorem inherited_ready : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited := by
  obtain ⟨output,after,done,valid,ready,steps,readback,classes⟩ := SourceEqualityConstraintAllocation.construct_complete
    plain.equalities SourceEqualityGuardReadback.empty_cached firstAllocation.2
    (SourceEqualityOriginalAllocationHistory.construct_steps own own_cached Cache.emptyState Cache.empty_valid
      first firstAllocation.2 (by cbv)).1
  have resultEq : output = inherited := Except.ok.inj ((congrArg Prod.fst done).symm.trans (by cbv))
  have stateEq : after = secondAllocation.2 := (congrArg Prod.snd done).symm
  subst output
  subst after
  exact ready
private theorem actual : call = .done result call.state call.fourth call.memo := by cbv

private theorem witness :
    built = .done value heap ∧
    SourceCurrentNativeOperationHeap.Good before ∧
    (∃ entry body depth ordinary, values[0]? = some (.mu entry body depth ordinary)) ∧
    (∃ entry body depth ordinary, values[1]? = some (.mu entry body depth ordinary)) ∧
    values[0]? ≠ values[1]? ∧
    call = .done result call.state call.fourth call.memo ∧
    SourceCurrentConstrainedCapGuardHeap.Heap annotation call.state.native.machine.heap := by
  refine ⟨constructed,good,?_,?_,?_,actual,?_⟩
  · cbv; exact ⟨_,_,_,_,rfl⟩
  · cbv; exact ⟨_,_,_,_,rfl⟩
  · cbv; intro impossible; cases impossible
  · exact SourceCurrentParentGuardHeapReturns.parent annotation actual good
      (SourceCurrentMemoMergeEffects.stored_empty _) guards
      (fun _ => ⟨root_field,inherited_ready,available⟩)

/-- A source-built parent with two distinct recursive operands retains its initial causal guard predicate. -/
theorem recursive_parent_retains_guards :
    built = .done value heap ∧
    SourceCurrentNativeOperationHeap.Good before ∧
    (∃ entry body depth ordinary, values[0]? = some (.mu entry body depth ordinary)) ∧
    (∃ entry body depth ordinary, values[1]? = some (.mu entry body depth ordinary)) ∧
    values[0]? ≠ values[1]? ∧
    call = .done result call.state call.fourth call.memo ∧
    SourceCurrentConstrainedCapGuardHeap.Heap annotation call.state.native.machine.heap := witness

end
end MicroCFTA.ParentGuardsCheck
