import MicroCFTA.SourceCurrentSeededProjectionCarrier
import MicroCFTA.SourceCurrentSecondarySeededSupport
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.SourceMemoGate

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ProjectionCarrierKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentSecondaryTrace SourceCurrentSecondaryProjectionScoped
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("step", .top) top [.var 0], .mk ("end", .top) top []])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def recursive : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def children : List (Value Symbol Guard) := [recursive, .reference .depth]
private def madeEdge := run (makeEdge ("parent", .top) top children) heap
private def madeNode := run (makeNode [madeEdge.1]) madeEdge.2
private def parent := madeNode.1
private def final := madeNode.2
private def forest : List (Value Symbol Guard) := [parent, .reference .depth]
private def paths : EqualityNormalize.Class := [[0, 0], [0, 0], [7]]

private theorem constructed : built = .done recursive heap := by cbv
private theorem source_semantic : SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression recursive heap constructed
private theorem source_available : Available heap recursive :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result recursive heap constructed
private theorem source_costs : CostHeap heap := InternedFreshOrdinaryCosts.closed_heap expression
private theorem depth_available (state : State Symbol Guard) : Available state (.reference .depth) :=
  reference_available state .depth (by
    intro identity impossible
    simp only [Value.free, List.mem_singleton, reduceCtorEq] at impossible)
private theorem children_available : Values heap children := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact source_available
  · have same := List.mem_singleton.mp member
    cases same
    exact depth_available heap
private theorem edge_invariants : Keeps heap madeEdge.2 ∧ EdgeResident madeEdge.2 madeEdge.1 ∧
    SemanticReady madeEdge.2 ∧ CostHeap madeEdge.2 := by
  have physical := SourceEqualityRequiredCache.edge ("parent", FullSyntax.Formula.top) top children heap source_semantic.ready children_available
  exact ⟨physical.1, physical.2.1,
    SourceEqualityRequiredSemanticCache.edge ("parent", FullSyntax.Formula.top) top children heap source_semantic children_available,
    source_costs⟩
private theorem node_invariants : SemanticReady final ∧ CostHeap final ∧ Available final parent := by
  have resident : Edges madeEdge.2 [madeEdge.1] := fun value member =>
    (List.mem_singleton.mp member) ▸ edge_invariants.2.1
  have checked := SourceEqualityOpenOrdinaryHead.node [madeEdge.1] madeEdge.2 edge_invariants.2.2.1 resident
  exact ⟨checked.2.1,
    InternedFreshOrdinaryCostHeap.preserve madeEdge.2 final edge_invariants.2.2.2
      (InternedShallowHeap.makeNode_noNewMu [madeEdge.1] madeEdge.2), checked.2.2.1⟩
private theorem forest_available : Values final forest := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact node_invariants.2.2
  · have same := List.mem_singleton.mp member
    cases same
    exact depth_available final
private theorem parent_open : parent.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem forest_open : ¬MergedColdReaderClosedInputs.ClosedValues forest := by
  intro closed
  exact parent_open (closed parent List.mem_cons_self)
private theorem recursive_shape : ∃ entry body depth ordinary,
    recursive = .mu entry body depth ordinary := by
  cases same : recursive with
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, rfl⟩
  | empty | reference | node | union => cbv at same; cases same
private theorem recursive_closed : recursive.free = [] := by cbv
private theorem endpoint_false : NodeTrace SourceMemoGate.unconstrained [] recursive final false final := by
  obtain ⟨entry, body, depth, ordinary, same⟩ := recursive_shape
  rw [same]
  have closed : (Value.mu entry body depth ordinary).free = [] := same ▸ recursive_closed
  cases test : SourceMemoGate.unconstrained (.mu entry body depth ordinary) with
  | false => simpa only [closed, List.isEmpty_nil, Bool.not_true] using NodeTrace.constrained (path := []) (state := final) test
  | true => exact .closed test (by simp only [closed, List.isEmpty_nil])
private theorem selected_false : PathTrace SourceMemoGate.unconstrained forest [0, 0] final false final := by
  apply PathTrace.child
  apply ChildTrace.present (value := parent) rfl
  have rows : nodeEdges parent = [madeEdge.1] := by cbv
  have depth : parent.depth = 1 := by cbv
  have free : parent.free = [.depth] := by cbv
  have shape : ∃ entry, parent = .node entry [madeEdge.1] 1 [.depth] := by
    cases same : parent with
    | node entry rows' depth' free' =>
        simp only [same, nodeEdges] at rows
        simp only [same, Value.depth] at depth
        simp only [same, Value.free] at free
        exact ⟨entry, by simp only [rows, depth, free]⟩
    | empty | reference | union | mu => cbv at same; cases same
  obtain ⟨entry, shape⟩ := shape
  rw [shape]
  apply NodeTrace.branches (by rfl)
  apply EdgesTrace.next
  · apply ChildTrace.present (value := recursive) (by cbv)
    exact endpoint_false
  · exact .nil
private theorem missing_false : PathTrace SourceMemoGate.unconstrained forest [7] final false final :=
  .child (.missing (by rfl))
private theorem original_gate : ClassTrace SourceMemoGate.unconstrained forest paths final false final :=
  .next selected_false (.next selected_false (.next missing_false .nil))
private theorem proper : ∀ path ∈ paths, path ≠ [] := by
  intro path member
  simp only [paths, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [ne_eq, List.cons_ne_nil, not_false_eq_true]

private def Carrier (state : State Symbol Guard) : Prop :=
  SourceEqualityAnnotationHeap.Heap (fun guard => guard = top) state
private theorem initial_carrier : Carrier final := by
  have allowed : SourceEqualityAnnotationConstruction.Allowed (fun guard : Guard => guard = top) expression := by
    simp only [expression, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]
    exact ⟨trivial, ⟨trivial, trivial⟩, trivial, trivial, trivial⟩
  have source : Carrier heap := SourceEqualityAnnotationConstruction.build _ expression allowed [] empty
    (SourceEqualityAnnotationHeap.empty_heap _)
  have first := SourceEqualityAnnotationHeap.run _ _
    (SourceEqualityAnnotationHeap.makeEdge (fun guard : Guard => guard = top) ("parent", FullSyntax.Formula.top)
      top children rfl) heap source
  exact SourceEqualityAnnotationHeap.run _ _
    (SourceEqualityAnnotationHeap.makeNode _ [madeEdge.1]) madeEdge.2 first
private theorem selected_support : PathSupport SourceMemoGate.unconstrained final [0, 0] forest := by
  have all := SourceCurrentSecondarySeededSupport.class_support SourceMemoGate.unconstrained original_gate
    node_invariants.1 node_invariants.2.1 forest_available proper
  exact all.2.2.2.2.2.2 [0, 0] (List.mem_map.mpr ⟨[0, 0], List.mem_cons_self, rfl⟩)

/-- Own finite projection below an open parent retains the original singleton guard carrier. -/
theorem constructed_forest_carrier :
    ¬MergedColdReaderClosedInputs.ClosedValues forest ∧
      ∃ result after, SourceEqualityProjectionGraph.Forest [0, 0] forest final result after ∧
        Carrier after ∧ Keeps final after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨natural, same, support⟩ := selected_support
  obtain ⟨result, after, actual, kept, semantic, available, closed⟩ :=
    SourceCurrentSecondaryProjectionComplete.forest_complete SourceMemoGate.unconstrained final node_invariants.1
      (SourceCurrentClassGateCompletion.gate_ready node_invariants.1 node_invariants.2.1) natural forest final
      node_invariants.1 forest_available (grows_refl _) support
  have carrier := SourceCurrentSeededProjectionCarrier.forest (fun guard => guard = top) SourceMemoGate.unconstrained final
    node_invariants.1 (SourceCurrentClassGateCompletion.gate_ready node_invariants.1 node_invariants.2.1) natural actual
    node_invariants.1 forest_available (grows_refl _) support initial_carrier
  rw [← same] at actual
  exact ⟨forest_open, result, after, actual, carrier, kept, semantic, available, closed⟩

private def checked (width : Nat) : SourceEqualityNativeDemand.State width :=
  ⟨SourceRecursiveIntersectionThunks.initial width ⟨final, Cache.emptyState⟩,
    SourceEqualityConstraintMemoAllocation.initial Cache.emptyState⟩

/-- The actual checked operand keeps equality operations, both native tables, and domain cache literal. -/
theorem constructed_checked_operand (width : Nat) :
    ∃ result after, SourceCurrentAllocatedSeededQuery.Operand [0, 0] forest (checked width) result after ∧
      Carrier after.native.machine.heap ∧ result.free = [] ∧
      after.operations = (checked width).operations ∧
      after.native.nodes = (checked width).native.nodes ∧ after.native.edges = (checked width).native.edges ∧
      after.native.machine.domains = (checked width).native.machine.domains := by
  obtain ⟨natural, same, support⟩ := selected_support
  obtain ⟨result, heap, projected, _kept, _semantic, _available, closed⟩ :=
    SourceCurrentSecondaryProjectionComplete.forest_complete SourceMemoGate.unconstrained final node_invariants.1
      (SourceCurrentClassGateCompletion.gate_ready node_invariants.1 node_invariants.2.1) natural forest final
      node_invariants.1 forest_available (grows_refl _) support
  rw [← same] at projected
  let after := SourceCurrentAllocatedQueryMemo.advancePhysical (checked width) ⟨heap, (checked width).operations⟩
  have actual : SourceCurrentAllocatedSeededQuery.Operand [0, 0] forest (checked width) result after :=
    .force result heap projected
  have carrier := SourceCurrentSeededProjectionCarrier.operand (fun guard => guard = top) SourceMemoGate.unconstrained final
    node_invariants.1 (SourceCurrentClassGateCompletion.gate_ready node_invariants.1 node_invariants.2.1) actual
    node_invariants.1 forest_available (grows_refl _) selected_support initial_carrier
  exact ⟨result, after, actual, carrier, closed, rfl, rfl, rfl, rfl⟩

private def projected := SourceEqualityProjectionWorker.forest 3 4 [0, 0] forest final
private def output : Value Symbol Guard := match projected with | .done value _ => value | _ => .empty
private def projectedHeap : State Symbol Guard := match projected with | .done _ heap => heap | _ => final
private theorem projected_done : projected = .done output projectedHeap := by cbv
private theorem projected_growth : final.nodes.next < projectedHeap.nodes.next ∧ final.edges.next < projectedHeap.edges.next := by
  cbv
  omega
private theorem warm_done : SourceEqualityProjectionWorker.forest 3 4 [0, 0] forest projectedHeap =
    .done output projectedHeap := by cbv

/-- The actual selected projection allocates on its first return and reuses the exact full heap on repetition. -/
theorem allocating_warm_carrier :
    SourceEqualityProjectionWorker.forest 3 4 [0, 0] forest final = .done output projectedHeap ∧
      final.nodes.next < projectedHeap.nodes.next ∧ final.edges.next < projectedHeap.edges.next ∧
      Carrier projectedHeap ∧ SourceEqualityProjectionWorker.forest 3 4 [0, 0] forest projectedHeap =
        .done output projectedHeap := by
  have graph := SourceEqualityProjectionWorkerSound.forest_graph 3 4 [0, 0] forest final output projectedHeap projected_done
  have support := SourceCurrentSecondaryProjectionComplete.false_path_support selected_false (by decide) forest_available
  have carrier := SourceCurrentSeededProjectionCarrier.forest (fun guard => guard = top) SourceMemoGate.unconstrained final
    node_invariants.1 (SourceCurrentClassGateCompletion.gate_ready node_invariants.1 node_invariants.2.1) [0, 0] graph
    node_invariants.1 forest_available (grows_refl _) support initial_carrier
  exact ⟨projected_done, projected_growth.1, projected_growth.2, carrier, warm_done⟩

end MicroCFTA.ProjectionCarrierKernels

#check @MicroCFTA.ProjectionCarrierKernels.constructed_forest_carrier
#print axioms MicroCFTA.ProjectionCarrierKernels.constructed_forest_carrier
#check @MicroCFTA.ProjectionCarrierKernels.constructed_checked_operand
#print axioms MicroCFTA.ProjectionCarrierKernels.constructed_checked_operand

#check @MicroCFTA.ProjectionCarrierKernels.allocating_warm_carrier
#print axioms MicroCFTA.ProjectionCarrierKernels.allocating_warm_carrier
