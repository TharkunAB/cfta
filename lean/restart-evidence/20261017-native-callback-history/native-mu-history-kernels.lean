import MicroCFTA.SourceCurrentNativeMuHistory
import MicroCFTA.InternedFreshOrdinaryCoverage
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

namespace MicroCFTA.NativeMuHistoryKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (History)
private def pair : Nat × Nat := (0,1)
private def old : Reference := .intersection pair.1 pair.2
private def expression : Syntax Nat Bool := .node [.mk 0 false [
  .var 0, .binder false (.node [.mk 1 true [.var 1,.var 0]])]]
private def built := build expression [.reference old] empty
private def body : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem actual : built = .done body heap := by cbv
private theorem inputs : InternedNestedProvenance.Values (empty : State Nat Bool) [.reference old] := by
  intro value member
  cases List.mem_singleton.mp member
  exact reference_available empty old (by simp [InternedFreshProbeKeys.IssuedReferences,Value.free,old])
private theorem semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap := by
  simpa only [built,heap] using SourceRecursiveIntersectionSemanticHeap.source expression [.reference old]
    empty SourceRecursiveIntersectionSemanticHeap.empty_heap inputs
private theorem available : Available heap body :=
  (InternedFreshOrdinaryFacts.build_verified expression [.reference old] empty InternedNestedFacts.empty_facts inputs).result
    body heap actual
private theorem covered : Covered [] heap :=
  InternedFreshOrdinaryCoverage.build_covered expression [.reference old] empty InternedConstructorTemplates.empty_valid
    InternedRecordCoherence.empty_correct.2 body heap actual
private theorem initialHistory : Nonempty (History empty heap) :=
  SourceCurrentNativeMuPublication.build_history expression [.reference old] empty
    ⟨SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
      [.reference old] inputs, SourceRecursiveIntersectionSemanticHeap.empty_heap.2⟩
private theorem used : old ∈ body.free := by cbv; exact .head _
private def nestedValue : Value Nat Bool := ((children body)[1]?).getD .empty
private def fields (value : Value Nat Bool) : Interned InternedBinderProtocol.NodeKey ×
    Value Nat Bool × Value Nat Bool × Value Nat Bool :=
  match value with
  | .mu entry actualBody depth ordinary => (entry,actualBody,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private theorem nested_shape : nestedValue = .mu (fields nestedValue).1 (fields nestedValue).2.1
    (fields nestedValue).2.2.1 (fields nestedValue).2.2.2 := by cbv
private theorem nested_member : nestedValue ∈ children body := by cbv; exact .tail _ (.head _)
private theorem nested : ∃ entry actualBody depth ordinary,
    (.mu entry actualBody depth ordinary : Value Nat Bool) ∈ children body := by
  refine ⟨(fields nestedValue).1,(fields nestedValue).2.1,(fields nestedValue).2.2.1,
    (fields nestedValue).2.2.2,?_⟩
  rw [← nested_shape]
  exact nested_member

private theorem produced_proof :
    old ∈ body.free ∧
    (∃ entry actualBody depth ordinary, (.mu entry actualBody depth ordinary : Value Nat Bool) ∈ children body) ∧
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body heap = .done value after ∧
      Nonempty (History heap after) ∧ Nonempty (History empty after) ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body after = .done value after := by
  obtain ⟨value,after,done,_context,_depth,_covered,_available,_growth,_history⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete_decoded pair body heap semantic.1 available semantic.2 covered
  have nativeHistory : Nonempty (History heap after) := by
    simpa only [done,Outcome.state] using SourceCurrentNativeMuHistory.maybeMu pair body heap semantic available
  obtain ⟨first⟩ := initialHistory
  obtain ⟨next⟩ := nativeHistory
  exact ⟨used,nested,value,after,done,⟨next⟩,⟨.trans first next⟩,
    SourceRecursiveIntersectionMaybeMu.replay pair body heap after after semantic.1.normal.facts available value done
      (grows_refl after)⟩

/-- A used native pair with an actual nested Mu has its own complete and exact warm histories. -/
theorem produced :
    old ∈ body.free ∧
    (∃ entry actualBody depth ordinary, (.mu entry actualBody depth ordinary : Value Nat Bool) ∈ children body) ∧
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body heap = .done value after ∧
      Nonempty (History heap after) ∧ Nonempty (History empty after) ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body after = .done value after := produced_proof
end MicroCFTA.NativeMuHistoryKernels
#check @MicroCFTA.NativeMuHistoryKernels.produced
#print MicroCFTA.NativeMuHistoryKernels.produced
#print axioms MicroCFTA.NativeMuHistoryKernels.produced
