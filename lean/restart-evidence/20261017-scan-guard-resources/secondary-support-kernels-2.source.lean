import MicroCFTA.SourceCurrentSecondarySeededSupport
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

namespace MicroCFTA.SecondarySeededSupportKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
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
private theorem parent_open : parent.free ≠ [] := by cbv
private theorem forest_open : ¬MergedColdReaderClosedInputs.ClosedValues forest := by
  intro closed
  exact parent_open (closed parent List.mem_cons_self)
private theorem recursive_shape : ∃ entry body depth ordinary,
    recursive = .mu entry body depth ordinary := by exact ⟨_, _, _, _, rfl⟩
private theorem recursive_closed : recursive.free = [] := by cbv
private theorem endpoint_false : NodeTrace SourceMemoGate.unconstrained [] recursive final false final := by
  obtain ⟨entry, body, depth, ordinary, same⟩ := recursive_shape
  cases same
  cases test : SourceMemoGate.unconstrained (.mu entry body depth ordinary) with
  | false => simpa only [recursive_closed, List.isEmpty_nil, Bool.not_true] using NodeTrace.constrained (path := []) (state := final) test
  | true => exact .closed test (by simpa only [recursive_closed])
private theorem selected_false : PathTrace SourceMemoGate.unconstrained forest [0, 0] final false final := by
  apply PathTrace.child
  apply ChildTrace.present (value := parent) rfl
  change NodeTrace SourceMemoGate.unconstrained [0]
    (.node _ [madeEdge.1] _ _) final false final
  apply NodeTrace.branches (by cbv)
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
  simp only [paths, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  rcases member with rfl | rfl <;> simp only [ne_eq, List.cons_ne_nil, not_false_eq_true]

/-- A productive source Mu lies below an open parent. Duplicate and missing proper paths keep their exact support. -/
theorem constructed_open_support :
    (∃ entry body depth ordinary, recursive = .mu entry body depth ordinary) ∧
      parent.free ≠ [] ∧ ¬MergedColdReaderClosedInputs.ClosedValues forest ∧
      ClassTrace SourceMemoGate.unconstrained forest paths final false final ∧
      (∀ path ∈ paths.map (List.map Int.ofNat), path ≠ []) ∧
      (∀ path ∈ paths.map (List.map Int.ofNat), PathSupport SourceMemoGate.unconstrained final path forest) := by
  have supported := SourceCurrentSecondarySeededSupport.class_support SourceMemoGate.unconstrained original_gate
    node_invariants.1 node_invariants.2.1 forest_available proper
  exact ⟨recursive_shape, parent_open, forest_open, supported.2.2.2.2.2.1,
    SourceCurrentSecondarySeededSupport.mapped_proper proper, supported.2.2.2.2.2.2⟩

/-- A false empty path does not imply root support for an open forest. -/
theorem root_path_boundary :
    ClassTrace SourceMemoGate.unconstrained forest [[]] final false final ∧
      ¬PathSupport SourceMemoGate.unconstrained final [] forest := by
  refine ⟨.next .empty .nil, ?_⟩
  rintro ⟨natural, same, support⟩
  have empty : natural = [] := List.map_eq_nil_iff.mp same.symm
  cases empty
  exact forest_open support

end MicroCFTA.SecondarySeededSupportKernels

#check @MicroCFTA.SecondarySeededSupportKernels.constructed_open_support
#print axioms MicroCFTA.SecondarySeededSupportKernels.constructed_open_support
#check @MicroCFTA.SecondarySeededSupportKernels.root_path_boundary
#print axioms MicroCFTA.SecondarySeededSupportKernels.root_path_boundary
