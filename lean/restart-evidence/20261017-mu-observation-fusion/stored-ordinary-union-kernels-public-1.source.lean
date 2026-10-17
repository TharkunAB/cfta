import MicroCFTA.SourceCurrentStoredOrdinaryUnionObservations
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
import MicroCFTA.SourceCurrentStoredReconstructionReplay

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

namespace MicroCFTA.StoredOrdinaryUnionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredNodeExpansion (Expansion)

private def captures : List (Value Nat Bool) := [.reference (.uninterned 0)]
private def recursive : Syntax Nat Bool := .binder false (.node [.mk 7 false [.var 0]])
private def expression : Syntax Nat Bool := .node [.mk 9 true [
  .node [.mk 1 false [recursive], .mk 2 true []],
  .node [.mk 3 false [recursive], .mk 4 true [.var 0]]]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def first : Value Nat Bool := ((children root)[0]?).getD .empty
private def second : Value Nat Bool := ((children root)[1]?).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × List (EdgeValue Nat Bool) × Nat × List Reference
  | .node entry rows level free => (entry,rows,level,free)
  | _ => (⟨0,.node []⟩,[],0,[])
private def environment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 0 then some .empty else none

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
  · cases found; exact InternedProbeProvenance.empty_available heap
  · cases found
private theorem firstShape : first = .node (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2 := by cbv
private theorem secondShape : second = .node (fields second).1 (fields second).2.1 (fields second).2.2.1 (fields second).2.2.2 := by cbv
private def originals : List (Value Nat Bool) := [first, second]
private def normalized := run (makeUnion originals) heap
private def parentCall := execute normalized.1 environment normalized.2
private def parentResult : Value Nat Bool := match parentCall with | .done value _ => value | .pending .. => .empty
private theorem parentDone : parentCall = .done parentResult parentCall.state := by cbv
private theorem originalsAvailable : Values heap originals := by
  intro value member
  rcases List.mem_cons.mp member with rfl | later
  · exact available.1
  · exact (List.mem_singleton.mp later) ▸ available.2
private theorem originalsOrdinary : ∀ value ∈ originals, SourceEqualityRequiredCache.Ordinary value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | later
  · cbv
  · rw [List.mem_singleton.mp later]
    cbv
private theorem normalizedKeeps : Keeps heap normalized.2 :=
  SourceEqualityNativeDemandHeapPrimitives.work_keeps (makeUnion originals) heap ready (.union originals originalsAvailable)
private theorem normalizedAvailable : Available normalized.2 normalized.1 :=
  (InternedNestedFacts.union_verified originals heap ready.semantic.1.normal.facts originalsAvailable).result _ _ rfl
private theorem parentKeeps : Keeps normalized.2 parentCall.state ∧ Available parentCall.state parentResult := by
  obtain ⟨result,after,done,kept,resultAvailable,_⟩ :=
    SourceCurrentStoredReconstruction.execute normalized.1 environment normalized.2 normalizedKeeps.ready normalizedAvailable
      (fun name value found => normalizedKeeps.available value (replacements name value found))
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (parentDone.symm.trans done)
  exact ⟨kept,resultAvailable⟩

/-- Actual ordinary merging precedes reconstruction and the original ordered calls share the final warm row observations. -/
theorem ordinary_merge :
    build expression captures empty = .done root heap ∧ Ready heap ∧ Values heap originals ∧
    (nodeEdges normalized.1).length = 4 ∧ (nodeEdges parentResult).length = 3 ∧
    execute normalized.1 environment normalized.2 = .done parentResult parentCall.state ∧
    ∃ outputs common,
      SourceCurrentStoredSubstitutionCalls.Calls environment originals parentCall.state outputs common ∧
      Keeps heap common ∧ Available common parentResult ∧
      run (makeUnion originals) common = (normalized.1, common) ∧
      execute normalized.1 environment common = .done parentResult common ∧
      Language.All₂ (fun original output => execute original environment common = .done output common) originals outputs ∧
      ∀ depth view, SourceCurrentOpenObservations.Same depth view [parentResult] outputs := by
  have whole := normalizedKeeps.trans parentKeeps.1
  obtain ⟨outputs,common,calls,kept,outputsAvailable⟩ := SourceCurrentStoredUnionObservations.members originals
    environment parentCall.state whole.ready
    (fun value member => whole.available value (originalsAvailable value member))
    (fun name value found => whole.available value (replacements name value found))
  have finalKeeps := whole.trans kept
  have warmMade := InternedConstructorTemplates.replay (makeUnion originals) heap common
    ready.semantic.1.normal.facts.coherent.valid (parentKeeps.1.trans kept).growth
  have warmParent := InternedFreshOrdinaryReplay.build_replay
    (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves normalized.1) [] normalized.1)
    ((InternedStoredSubstitution.leaves normalized.1).map (InternedStoredSubstitution.input environment))
    normalized.2 common parentResult parentCall.state normalizedKeeps.ready.semantic.1.normal.facts.coherent.valid parentDone kept.growth
  have warmChildren := SourceCurrentStoredCallsReplay.replay calls common whole.ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
  have observed := SourceCurrentStoredOrdinaryUnionObservations.warm finalKeeps.ready
    (fun value member => finalKeeps.available value (originalsAvailable value member))
    (fun name value found => finalKeeps.available value (replacements name value found))
    originalsOrdinary warmChildren warmMade warmParent
  exact ⟨actual,ready,originalsAvailable,by cbv,by cbv,parentDone,outputs,common,calls,finalKeeps,
    kept.available parentResult parentKeeps.2,warmMade,warmParent,warmChildren,observed⟩

end MicroCFTA.StoredOrdinaryUnionKernels

#check @MicroCFTA.StoredOrdinaryUnionKernels.ordinary_merge
#print axioms MicroCFTA.StoredOrdinaryUnionKernels.ordinary_merge
