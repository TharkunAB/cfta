import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentStoredUnionWarm
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
namespace MicroCFTA.StoredUnionWarmKernels
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
open Language
private def originals : List (Value Nat Bool) := (fields first).2.1
private theorem warm_proof :
    ∃ result after outputs middle,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment originals heap outputs middle ∧ outputs.length = 3 ∧
      run (makeUnion originals) after = (first,after) ∧
      InternedFreshOrdinaryStoredSubstitution.execute first environment after = .done result after ∧
      ∀ depth view, Same depth view [result] outputs := by
  have sourceAvailable := available.1
  rw [firstShape] at sourceAvailable
  obtain ⟨result,after,outputs,middle,done,calls,kept,_,_,_,growth,_⟩ :=
    SourceCurrentStoredUnionObservations.complete (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2
      environment heap ready sourceAvailable replacements
  rw [←firstShape] at done
  have warm := SourceCurrentStoredCallsReplay.replay calls after ready.semantic.1.normal.facts.coherent.valid growth
  have originalMade : run (makeUnion originals) heap = (first,heap) := by cbv
  have made : run (makeUnion originals) after = (first,after) := by
    simpa only [originalMade] using InternedConstructorTemplates.replay (makeUnion originals) heap after
      ready.semantic.1.normal.facts.coherent.valid (by simpa only [originalMade] using kept.growth)
  have called : InternedFreshOrdinaryStoredSubstitution.execute first environment after = .done result after :=
    InternedFreshOrdinaryReplay.build_replay _ _ heap after result after
      ready.semantic.1.normal.facts.coherent.valid done (grows_refl _)
  have selected : distinctNodes (originals.flatMap unionMembers) = originals := by cbv
  have selectedAvailable : Values after originals := by
    intro value member
    exact kept.available value (sourceAvailable.children value member)
  have observed := SourceCurrentStoredUnionWarm.warm environment after originals originals outputs first result
    kept.ready selectedAvailable (fun name value found => kept.available value (replacements name value found))
    selected warm made called
  exact ⟨result,after,outputs,middle,done,calls,calls.length.trans (by cbv),made,called,observed⟩
/-- A source-built open union with a productive Mu has an exact warm constructor and reconstruction with observed ordered member results. -/
theorem warm :
    ∃ result after outputs middle,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment originals heap outputs middle ∧ outputs.length = 3 ∧
      run (makeUnion originals) after = (first,after) ∧
      InternedFreshOrdinaryStoredSubstitution.execute first environment after = .done result after ∧
      ∀ depth view, Same depth view [result] outputs := warm_proof
end MicroCFTA.StoredUnionWarmKernels
#check @MicroCFTA.StoredUnionWarmKernels.warm
#print MicroCFTA.StoredUnionWarmKernels.warm
#print axioms MicroCFTA.StoredUnionWarmKernels.warm
