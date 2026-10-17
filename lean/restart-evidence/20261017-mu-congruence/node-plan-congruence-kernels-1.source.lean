import MicroCFTA.SourceCurrentNodePlanCongruence
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
namespace MicroCFTA.NodePlanCongruenceKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryPlanEquivalence
open InternedNestedProvenance (Values)
open SourceCurrentNodePlanCongruence
open SourceEqualityRequiredCache (Ready Keeps)

private def firstInputs : List (Value Nat Bool) := [.reference .depth, .reference (.uninterned 1)]
private def secondInputs : List (Value Nat Bool) := [.reference (.uninterned 1), .reference .depth]
private def a : EdgeSyntax Nat Bool :=
  .mk 0 false [.var 0, .binder false (.node [.mk 7 true [.var 0, .var 1]])]
private def aOther : EdgeSyntax Nat Bool :=
  .mk 0 false [.var 1, .binder false (.node [.mk 7 true [.var 0, .var 2]])]
private def b : EdgeSyntax Nat Bool := .mk 1 true [.var 1]
private def bOther : EdgeSyntax Nat Bool := .mk 1 true [.var 0]
private def dead : EdgeSyntax Nat Bool := .mk 2 false [.empty]
private def firstRows : List (EdgeSyntax Nat Bool) := [a, b, dead]
private def secondRows : List (EdgeSyntax Nat Bool) := [dead, bOther, aOther, aOther]

private theorem a_related : RowEquivalent a firstInputs aOther secondInputs := by
  simp [RowEquivalent, a, aOther, firstInputs, secondInputs, ManyEquivalent, Equivalent, EdgesEquivalent]
private theorem b_related : RowEquivalent b firstInputs bOther secondInputs := by
  simp [RowEquivalent, b, bOther, firstInputs, secondInputs, ManyEquivalent, Equivalent]
private theorem dead_related : RowEquivalent dead firstInputs dead secondInputs := by
  simp [RowEquivalent, dead, ManyEquivalent, Equivalent]
private theorem related : RowsEquivalent firstRows firstInputs secondRows secondInputs := by
  constructor
  · intro row member
    simp only [firstRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨aOther, by simp [secondRows], a_related⟩
    · exact ⟨bOther, by simp [secondRows], b_related⟩
    · exact ⟨dead, by simp [secondRows], dead_related⟩
  · intro row member
    simp only [secondRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨dead, by simp [firstRows], dead_related⟩
    · exact ⟨b, by simp [firstRows], b_related⟩
    · exact ⟨a, by simp [firstRows], a_related⟩
    · exact ⟨a, by simp [firstRows], a_related⟩

private theorem ready : Ready (empty (Symbol := Nat) (Guard := Bool)) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty rfl
private theorem first_available : Values empty firstInputs := by
  intro value member
  simp only [firstInputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact InternedNestedProvenance.depth_available empty
  · exact InternedNestedProvenance.ordinary_available empty 1
private theorem second_available : Values empty secondInputs := by
  intro value member
  simp only [secondInputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact InternedNestedProvenance.ordinary_available empty 1
  · exact InternedNestedProvenance.depth_available empty

private def built := build (.node firstRows) firstInputs empty
private def result : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem actual : built = .done result heap := by cbv
private theorem two_rows : (nodeEdges result).length = 2 := by cbv
private theorem connected_proof :
    ∃ value middle after,
      build (.node firstRows) firstInputs empty = .done value middle ∧
      build (.node secondRows) secondInputs middle = .done value after ∧
      Keeps empty middle ∧ Keeps middle after ∧ Available after value ∧ (nodeEdges value).length = 2 := by
  obtain ⟨value, middle, after, firstDone, secondDone, first, second, available⟩ :=
    SourceCurrentNodePlanCongruence.initial firstRows secondRows firstInputs secondInputs empty ready
      first_available second_available related
  have same : value = result := by
    have equal := firstDone.symm.trans actual
    simpa only [Outcome.done.injEq] using (by injection equal with valueSame; exact valueSame)
  exact ⟨value, middle, after, firstDone, secondDone, first, second, available, same ▸ two_rows⟩

/-- Initial captured nested binders tolerate reordered duplicated rows and retain exactly two live rows. -/
theorem connected :
    ∃ value middle after,
      build (.node firstRows) firstInputs empty = .done value middle ∧
      build (.node secondRows) secondInputs middle = .done value after ∧
      Keeps empty middle ∧ Keeps middle after ∧ Available after value ∧ (nodeEdges value).length = 2 := connected_proof

end MicroCFTA.NodePlanCongruenceKernels
#check @MicroCFTA.NodePlanCongruenceKernels.connected
#print MicroCFTA.NodePlanCongruenceKernels.connected
#print axioms MicroCFTA.NodePlanCongruenceKernels.connected
