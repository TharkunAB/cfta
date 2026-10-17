import MicroCFTA.SourceCurrentStoredUnionFlattening
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
namespace MicroCFTA.StoredUnionFlatteningKernels
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
private def originals : List (Value Nat Bool) := [first,.empty,second,first]
private theorem originalsAvailable : Values heap originals := by
  intro value member
  simp only [originals,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact available.1
  · exact InternedTemplateProvenance.empty_available heap
  · exact available.2
  · exact available.1
/-- Source-built open and closed unions retain eight actual flattened calls, including repeated members. -/
theorem flattened_calls :
    ∃ outputs after flattened,
      Calls environment originals heap outputs after ∧ Keeps heap after ∧
      Language.All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment after = .done output after)
        (originals.flatMap unionMembers) flattened ∧ flattened.length = 8 ∧
      ∀ depth view, Same depth view outputs flattened := by
  obtain ⟨outputs,after,calls,kept,_⟩ := SourceCurrentStoredUnionObservations.members originals environment heap ready
    originalsAvailable replacements
  have warm := SourceCurrentStoredCallsReplay.replay calls after ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
  obtain ⟨flattened,paired,observed⟩ := SourceCurrentStoredUnionFlattening.warm originals outputs environment after kept.ready
    (fun value member => kept.available value (originalsAvailable value member))
    (fun name value found => kept.available value (replacements name value found)) warm
  exact ⟨outputs,after,flattened,calls,kept,paired,paired.length_eq.symm.trans (by cbv),observed⟩
end MicroCFTA.StoredUnionFlatteningKernels
#check @MicroCFTA.StoredUnionFlatteningKernels.flattened_calls
#print MicroCFTA.StoredUnionFlatteningKernels.flattened_calls
#print axioms MicroCFTA.StoredUnionFlatteningKernels.flattened_calls
