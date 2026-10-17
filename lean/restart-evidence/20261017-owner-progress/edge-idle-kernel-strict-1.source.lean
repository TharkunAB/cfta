import MicroCFTA.SourceCurrentOuterEdgeIdle
import MicroCFTA.SourceCurrentAllocatedPartialInitialization

set_option linter.all true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.OuterEdgeIdleKernels
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentOuterEdgeIdle (EdgeIdle Safe)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private def plain : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("root", .top) plain [.node [.mk ("leaf", .top) plain []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def row : EdgeValue Symbol Guard :=
  ((nodeEdges root)[0]?).getD (run (makeEdge ("root", .top) plain []) heap).1
private def inherited := SourceCurrentAllocatedPartialInitialization.emptyValue Cache.emptyState
private def cold := SourceCurrentAllocatedPartialInitialization.caller 8 Cache.emptyState heap
private def ancestor : NodeRequest := ⟨.contradiction,.empty⟩
private def before := (beginNode ancestor cold).2.2
private def request : NodeRequest := ⟨inherited,root⟩
private noncomputable def actual := SourceCurrentAllocatedPartialWorker.nodeCall 8 4 4 4 4 4 4 4 4 32 0 request before
private noncomputable def after := actual.state
private theorem built_done : built = .done root heap := by cbv
private theorem facts : InternedNestedFacts.Facts heap := (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem before_idle : EdgeIdle before :=
  SourceCurrentOuterEdgeIdle.initial cold.checked cold.merge cold.fourth
private theorem actual_done : actual = .done root after := by cbv

/-- A nonempty child traversal returns edge-idle while an independent node owner stays active. -/
theorem live_walk_with_active_node :
    ∃ (program : Syntax Symbol Guard) (value : Value Symbol Guard) (edge : EdgeValue Symbol Guard)
        (inherited : SourceEqualityConstraintAllocation.Value) (initial final : Caller 8) (owner : NodeRequest),
      InternedFreshOrdinaryConstruction.build program [] empty = .done value initial.checked.native.machine.heap ∧
      Available initial.checked.native.machine.heap value ∧ edge.children.length = 1 ∧
      initial.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧ EdgeIdle initial ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 8 4 4 4 4 4 4 4 4 32 0 ⟨inherited,value⟩ initial = .done value final ∧
      EdgeIdle final ∧ final.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
      beginEdge ⟨inherited,edge⟩ final = (0,.ready edge,final) := by
  have safe := SourceCurrentOuterEdgeIdle.node_call 8 4 4 4 4 4 4 4 4 32 0 request before before_idle
  change Safe actual at safe
  rw [actual_done] at safe
  refine ⟨expression,root,row,inherited,before,after,ancestor,built_done,available,?_,?_,before_idle,actual_done,safe,?_,?_⟩
  · cbv
  · cbv
  · cbv
  · cbv

/-- Edge-idle entry still permits a literal busy node failure. -/
theorem node_busy_remains_possible :
    ∃ (initial : Caller 8) (owner : NodeRequest),
      EdgeIdle initial ∧ initial.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 owner initial =
        .failed (.nodeMemo 0 .busy) initial ∧
      Safe (SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 owner initial) := by
  refine ⟨before,ancestor,before_idle,?_,?_,
    SourceCurrentOuterEdgeIdle.node_call 0 0 0 0 0 0 0 0 0 0 0 ancestor before before_idle⟩ <;> cbv

private def unprepared : Caller 8 := SourceCurrentAllocatedPartialState.initial
  ⟨SourceRecursiveIntersectionThunks.initial 8 ⟨heap,Cache.emptyState⟩,
    SourceEqualityConstraintMemoAllocation.initial Cache.emptyState⟩
  SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def edgeRequest : EdgeRequest := ⟨.contradiction,row⟩
private noncomputable def failed := SourceCurrentAllocatedPartialWorker.edgeCall
  0 0 0 0 0 0 0 0 0 0 0 edgeRequest unprepared

/-- A missing parent field propagates immediately and can retain its failed edge owner. -/
theorem failed_body_can_leave_edge_active :
    ∃ (request : EdgeRequest) (initial final : Caller 8),
      EdgeIdle initial ∧
      SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 0 request initial =
        .failed (.parent .missingField) final ∧
      Safe (SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 0 request initial) ∧
      final.edgeResults.cells 0 = some ⟨request,.evaluating⟩ ∧ ¬EdgeIdle final := by
  have idle : EdgeIdle unprepared := SourceCurrentOuterEdgeIdle.initial _ _ _
  have running : failed.state.edgeResults.cells 0 = some ⟨edgeRequest,.evaluating⟩ := by cbv
  refine ⟨edgeRequest,unprepared,failed.state,idle,?_,
    SourceCurrentOuterEdgeIdle.edge_call 0 0 0 0 0 0 0 0 0 0 0 edgeRequest unprepared idle,running,?_⟩
  · cbv
  · intro impossible
    exact impossible 0 edgeRequest running

end MicroCFTA.OuterEdgeIdleKernels

