import MicroCFTA.SourceCurrentStoredUnionObservations
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
namespace MicroCFTA.StoredUnionObservationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenObservations (Same)
open SourceCurrentStoredSubstitutionCalls (Calls)
private def captures : List (Value Nat Bool) := [.reference (.uninterned 0)]
private def recursive : Syntax Nat Bool := .binder false (.node [.mk 7 false [.var 0]])
private def plain : Syntax Nat Bool := .node [.mk 8 true []]
private def expression : Syntax Nat Bool := .node [.mk 0 true [
  .union [recursive,.var 0,plain],.union [recursive,plain]]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def first : Value Nat Bool := ((children root)[0]?).getD .empty
private def second : Value Nat Bool := ((children root)[1]?).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × List (Value Nat Bool) × Nat × List Reference
  | .union entry values level free => (entry,values,level,free)
  | _ => (⟨0,.union []⟩,[],0,[])
private def environment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 0 then some (.reference .depth) else none
private theorem actual : built = .done root heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  have same : value = .reference (.uninterned 0) := List.mem_singleton.mp member
  cases same
  exact InternedNestedProvenance.ordinary_available empty 0
private theorem ready : Ready heap := by
  have context := SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures inputs
  refine ⟨SourceRecursiveIntersectionSemanticHeap.source expression captures empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs,
    InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid
      InternedRecordCoherence.empty_correct.2 root heap actual,?_⟩
  exact (InternedOpenDepthExecution.build_depth expression captures empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedOpenDepthReadback.empty_heap).heap
private theorem available : Available heap first ∧ Available heap second := by
  have result := (InternedFreshOrdinaryFacts.build_verified expression captures empty InternedNestedFacts.empty_facts inputs).result root heap actual
  exact ⟨result.children first (by cbv; exact .head _), result.children second (by cbv; exact .tail _ (.head _))⟩
private theorem replacements : InternedStoredSubstitution.Replacements heap environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found; exact InternedNestedProvenance.depth_available heap
  · cases found
private theorem firstShape : first = .union (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2 := by cbv
private theorem secondShape : second = .union (fields second).1 (fields second).2.1 (fields second).2.2.1 (fields second).2.2.2 := by cbv
private theorem firstFree : first.free = [.uninterned 0] := by cbv
private theorem secondFree : second.free = [] := by cbv
private theorem open_proof :
    first.free ≠ [] ∧ (fields first).2.1.length = 3 ∧
    ∃ result after values middle,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment (fields first).2.1 heap values middle ∧
      values.length = 3 ∧ Keeps heap after ∧ Keeps heap middle ∧ Available after result ∧
      Values middle values ∧ Grows middle after ∧ ∀ depth view, Same depth view [result] values := by
  have sourceAvailable := available.1
  rw [firstShape] at sourceAvailable
  obtain ⟨result,after,values,middle,done,calls,kept,memberKept,output,memberAvailable,growth,observed⟩ :=
    SourceCurrentStoredUnionObservations.complete (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2
      environment heap ready sourceAvailable replacements
  rw [←firstShape] at done
  exact ⟨by rw [firstFree]; simp,by cbv,result,after,values,middle,done,calls,
    calls.length.trans (by cbv),kept,memberKept,output,memberAvailable,growth,observed⟩
/-- An actual open union with a productive Mu and bare reference retains all original ordered member observations. -/
theorem open_union :
    first.free ≠ [] ∧ (fields first).2.1.length = 3 ∧
    ∃ result after values middle,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment (fields first).2.1 heap values middle ∧
      values.length = 3 ∧ Keeps heap after ∧ Keeps heap middle ∧ Available after result ∧
      Values middle values ∧ Grows middle after ∧ ∀ depth view, Same depth view [result] values := open_proof
private theorem closed_proof :
    second.free = [] ∧ (fields second).2.1.length = 2 ∧
    InternedFreshOrdinaryStoredSubstitution.execute second environment heap = .done second heap ∧
    ∃ values middle,
      Calls environment (fields second).2.1 heap values middle ∧ values.length = 2 ∧
      Keeps heap middle ∧ Values middle values ∧ Grows middle heap ∧
      ∀ depth view, Same depth view [second] values := by
  have sourceAvailable := available.2
  rw [secondShape] at sourceAvailable
  obtain ⟨result,after,values,middle,done,calls,_,memberKept,_,memberAvailable,growth,observed⟩ :=
    SourceCurrentStoredUnionObservations.complete (fields second).1 (fields second).2.1 (fields second).2.2.1 (fields second).2.2.2
      environment heap ready sourceAvailable replacements
  rw [←secondShape] at done
  have closedDone := SourceCurrentStoredUnionObservations.closed second environment heap secondFree
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans closedDone)
  exact ⟨secondFree,by cbv,closedDone,values,middle,calls,calls.length.trans (by cbv),memberKept,memberAvailable,growth,observed⟩
/-- A source-built closed union retains its literal return and still supplies actual original member observations. -/
theorem closed_union :
    second.free = [] ∧ (fields second).2.1.length = 2 ∧
    InternedFreshOrdinaryStoredSubstitution.execute second environment heap = .done second heap ∧
    ∃ values middle,
      Calls environment (fields second).2.1 heap values middle ∧ values.length = 2 ∧
      Keeps heap middle ∧ Values middle values ∧ Grows middle heap ∧
      ∀ depth view, Same depth view [second] values := closed_proof
end MicroCFTA.StoredUnionObservationKernels
#check @MicroCFTA.StoredUnionObservationKernels.open_union
#print MicroCFTA.StoredUnionObservationKernels.open_union
#print axioms MicroCFTA.StoredUnionObservationKernels.open_union
#check @MicroCFTA.StoredUnionObservationKernels.closed_union
#print MicroCFTA.StoredUnionObservationKernels.closed_union
#print axioms MicroCFTA.StoredUnionObservationKernels.closed_union
