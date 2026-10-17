import MicroCFTA.SourceCurrentStoredNormalizedPlans
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace MicroCFTA.StoredNormalizedKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
private def captures : List (Value Nat Bool) :=
  [.reference (.uninterned 0), .reference (.uninterned 1), .reference (.uninterned 2)]
private def first : Syntax Nat Bool := .node [.mk 9 false [
  .binder false (.node [.mk 5 true [.var 1], .mk 5 true [.var 2], .mk 6 false [.var 0]])]]
private def second : Syntax Nat Bool := .node [.mk 9 false [
  .binder false (.node [.mk 6 false [.var 0], .mk 5 true [.var 3]])]]
private def expression : Syntax Nat Bool := .node [.mk 0 true [first, second]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Nat Bool := ((children root)[0]?).getD .empty
private def right : Value Nat Bool := ((children root)[1]?).getD .empty
private def nestedRows : Value Nat Bool → List (EdgeValue Nat Bool)
  | .node _ [.mk _ [.mu _ (.node _ rows _ _) _ _]] _ _ => rows
  | _ => []
private def firstEnv : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 0 ∨ name = .uninterned 1 then some (.reference .depth) else none
private def secondEnv : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 2 then some (.reference .depth) else none
private theorem actual : built = .done root heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact InternedNestedProvenance.ordinary_available empty 0
  · exact InternedNestedProvenance.ordinary_available empty 1
  · exact InternedNestedProvenance.ordinary_available empty 2
private theorem ready : Ready heap := by
  have context := SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures inputs
  refine ⟨SourceRecursiveIntersectionSemanticHeap.source expression captures empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs,
    InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid
      InternedRecordCoherence.empty_correct.2 root heap actual,?_⟩
  exact (InternedOpenDepthExecution.build_depth expression captures empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedOpenDepthReadback.empty_heap).heap
private theorem rootsAvailable : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.build_verified expression captures empty InternedNestedFacts.empty_facts inputs).result root heap actual
  exact ⟨available.children left (by cbv; exact .head _),available.children right (by cbv; exact .tail _ (.head _))⟩
private theorem related : SourceCurrentStoredNormalizedPlans.Related [] [] [] [] firstEnv secondEnv left right := by
  cbv
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, exists_prop, exists_eq_left]
  simp only [SourceCurrentStoredNormalizedPlans.RowRelated]
  cbv
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    exists_prop, or_and_right, exists_or, exists_eq_left]
  simp only [SourceCurrentStoredNormalizedPlans.RowRelated]
  cbv
private theorem leftFree : left.free = [.uninterned 0,.uninterned 1] := by cbv
private theorem rightFree : right.free = [.uninterned 2] := by cbv
private theorem produced_proof :
    left ≠ right ∧ left.free ≠ [] ∧ right.free ≠ [] ∧
    (nestedRows left).length = 3 ∧ (nestedRows right).length = 2 ∧
    ∃ value middle after,
      InternedFreshOrdinaryStoredSubstitution.execute left firstEnv heap = .done value middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute right secondEnv middle = .done value after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after value := by
  have calls := SourceCurrentStoredNormalizedPlans.complete left right firstEnv secondEnv heap ready rootsAvailable.1 rootsAvailable.2
    (by intro name value found; dsimp only [firstEnv] at found; split at found
        · cases found; exact InternedNestedProvenance.depth_available heap
        · cases found)
    (by intro name value found; dsimp only [secondEnv] at found; split at found
        · cases found; exact InternedNestedProvenance.depth_available heap
        · cases found) related
  refine ⟨?_,by rw [leftFree]; simp,by rw [rightFree]; simp,by cbv,by cbv,calls⟩
  intro same
  have different : left.free ≠ right.free := by rw [leftFree,rightFree]; simp
  exact different (congrArg Value.free same)
/-- Distinct open stored roots normalize nested Mu-body row multiplicity during two actual reconstructions. -/
theorem produced :
    left ≠ right ∧ left.free ≠ [] ∧ right.free ≠ [] ∧
    (nestedRows left).length = 3 ∧ (nestedRows right).length = 2 ∧
    ∃ value middle after,
      InternedFreshOrdinaryStoredSubstitution.execute left firstEnv heap = .done value middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute right secondEnv middle = .done value after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after value := produced_proof
end MicroCFTA.StoredNormalizedKernels
#check @MicroCFTA.StoredNormalizedKernels.produced
#print MicroCFTA.StoredNormalizedKernels.produced
#print axioms MicroCFTA.StoredNormalizedKernels.produced
