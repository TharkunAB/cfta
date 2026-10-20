import MicroCFTA.SourceCurrentOuterPlainOwnerProgress
import MicroCFTA.SourceCurrentAllocatedPartialInitialization

/-!
# An actual warm plain row dispatch after an earlier sibling

A closed binary source uses one plain leaf in both child slots.
An actual cold edge call creates the memo cell before owner activation.
The active owner then reads that same cell. The first child returns before
slot one. The generic theorem excludes the active owner at that dispatch.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000
namespace MicroCFTA.PlainOwnerFixture
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterExecutionAncestry (Reached Step)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq Node := by classical exact inferInstance
private def plain : Guard := ⟨some [], .top⟩
private def leafPlan : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def program : Syntax Symbol Guard := .node [.mk ("pair",.top) plain [leafPlan,leafPlan]]
private def built := InternedFreshOrdinaryConstruction.build program [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct plain.equalities Cache.emptyState
private def inherited := SourceCurrentAllocatedPartialInitialization.emptyValue allocated.2
private def initial := SourceCurrentAllocatedPartialInitialization.caller 8 allocated.2 heap
private def owner : NodeRequest := ⟨inherited,root⟩
private def row : Edge := (nodeEdges root)[0]?.getD (run (makeEdge ("pair",.top) plain []) heap).1
private noncomputable def cold := edgeCall 10 16 16 16 16 16 16 16 16 128 0 ⟨inherited,row⟩ initial
private noncomputable def warmed := cold.state
private noncomputable def running := (beginNode owner warmed).2.2
private noncomputable def parent := edgeCall 10 16 16 16 16 16 16 16 16 128 0 ⟨inherited,row⟩ running
private noncomputable def combined : EqValue :=
  match (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited parent.state.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def prefixed := SourceCurrentAllocatedPartialGraph.prefixState parent.state row inherited
private noncomputable def earlier := walk 10 16 16 16 16 16 16 16 16 128 0 combined 0 (row.children.take 1) prefixed
private noncomputable def dispatch := SourceCurrentAllocatedPartialGraph.descend earlier.state combined 1
private def selected : Node := (row.children[1]?).getD .empty
private theorem construction : built = .done root heap := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [plain] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
    (show allocated = (.ok inherited,allocated.2) by cbv)
private theorem initial_inputs : SourceCurrentOuterPrefixInvariants.Good initial ∧
    SourceCurrentOuterPrefixInvariants.NodeReady initial owner := by
  have source := SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid program
    (fun field member => by
      simp only [program,leafPlan,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> simp)
    root heap construction
  have eq := SourceCurrentAllocatedPartialInitialization.operations_correct allocated.2
    (history.verified Cache.empty_valid).1
  have good : SourceCurrentNativeOperationHeap.Good initial.checked :=
    ⟨⟨source.1.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,source.1.good.heap,eq.1,source.1.good.fields.grows eq.2.1,
      source.1.semantic,source.1.costs⟩
  exact ⟨SourceCurrentOuterPrefixInvariants.initial initial.checked _ _ good
    (SourceCurrentMemoMergeEffects.stored_empty heap)
    (SourceCurrentMuReconstructionEffects.constructed program root heap construction),eq.2.2,source.2.1⟩
private theorem row_list : nodeEdges root = [row] := by cbv
private theorem row_ready : SourceCurrentOuterPrefixInvariants.EdgeReady initial ⟨inherited,row⟩ := by
  refine ⟨initial_inputs.2.1,?_⟩
  exact resident_edges _ initial_inputs.1.checked.heap.semantic.1.normal.facts.linked root
    initial_inputs.2.2.resident row (by rw [row_list]; exact List.mem_singleton_self _)
private theorem cold_return : cold = .done row warmed := by cbv
private theorem began : beginNode owner warmed = (0,.evaluate owner,running) := by cbv
private theorem running_inputs : SourceCurrentOuterPrefixInvariants.Good running ∧
    SourceCurrentOuterPrefixInvariants.NodeReady running owner := by
  have next := SourceCurrentOuterPrefixInvariants.edge_done cold_return initial_inputs.1 row_ready
  exact SourceCurrentOuterPrefixInvariants.activate began next.1
    ⟨initial_inputs.2.1.grows next.2.1.operations.constraint_growth,
      next.2.1.keeps.available root initial_inputs.2.2⟩
private theorem running_origins : SourceCurrentOuterPlainRowShapes.Origins running := by
  have origins := (SourceCurrentOuterPlainRowShapes.edge_call cold_return initial_inputs.1 row_ready
    (SourceCurrentOuterPlainRowShapes.initial initial.checked _ _)).1
  exact origins
private theorem ordinary_shape (value : Node)
    (ordinary : (match value with | .node .. => true | _ => false) = true) :
    ∃ entry depth free, value = .node entry (nodeEdges value) depth free := by
  cases value <;> simp_all [nodeEdges]
private theorem ordinary : ∃ entry depth free, root = .node entry [row] depth free := by
  simpa only [row_list] using ordinary_shape root (by cbv)
private theorem parent_return : parent = .done row parent.state := by cbv
private theorem prefix_return :
    (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited parent.state.checked.operations).1 =
      .ok (some combined) := by cbv
private theorem earlier_return : earlier = .done [selected] earlier.state := by cbv
private theorem checked_dispatch :
    Reached 16 16 16 16 16 16 16 16 128 0 (.body 12 owner running)
      (.node 8 ⟨dispatch.1,selected⟩ dispatch.2) ∧
      selected.referenceOf ≠ root.referenceOf ∧
      (NodeRequest.mk dispatch.1 selected).key ≠ owner.key := by
  obtain ⟨entry,depth,free,shape⟩ := ordinary
  have past : Reached 16 16 16 16 16 16 16 16 128 0 (.body 12 owner running)
      (.rows 11 inherited [row] running) := .snoc (.refl _) (.body_rows shape)
  exact SourceCurrentOuterPlainOwnerProgress.dispatch (handle := 0) shape running_inputs.1 running_inputs.2
    (by cbv) running_origins past (by simp) (by cbv) parent_return prefix_return (by
      have live : combined = .live 0 [] := by cbv
      rw [live]
      intro impossible
      cases impossible)
    earlier_return (by cbv)

/-- Actual cold publication and warm reuse reach slot one with a distinct owner key. -/
theorem actual_warm_plain_dispatch :
    built = .done root heap ∧
    inherited.payload = some [] ∧
    cold = .done row warmed ∧
    beginNode owner warmed = (0,.evaluate owner,running) ∧
    (beginEdge ⟨inherited,row⟩ running).2.1 = .ready row ∧
    parent = .done row parent.state ∧
    earlier = .done [selected] earlier.state ∧
    dispatch.2.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
    Reached 16 16 16 16 16 16 16 16 128 0 (.body 12 owner running)
      (.node 8 ⟨dispatch.1,selected⟩ dispatch.2) ∧
    selected.referenceOf ≠ root.referenceOf ∧
    (NodeRequest.mk dispatch.1 selected).key ≠ owner.key := by
  exact ⟨construction,by cbv,cold_return,began,by cbv,parent_return,earlier_return,
    by cbv,checked_dispatch⟩
end MicroCFTA.PlainOwnerFixture
