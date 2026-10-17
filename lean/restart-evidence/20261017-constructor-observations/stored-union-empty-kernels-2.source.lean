import MicroCFTA.SourceCurrentStoredUnionEmpty
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
namespace MicroCFTA.StoredUnionEmptyKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenObservations (Same)
open SourceCurrentStoredSubstitutionCalls (Calls)
private def captures : List (Value Nat Bool) := [.reference (.uninterned 0),.reference (.uninterned 1)]
private def recursive : Syntax Nat Bool := .binder false (.node [.mk 7 false [.var 0]])
private def plain : Syntax Nat Bool := .node [.mk 8 true []]
private def expression : Syntax Nat Bool := .node [.mk 0 true [
  .union [.var 0,.var 1],.union [recursive,plain]]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def first : Value Nat Bool := ((children root)[0]?).getD .empty
private def second : Value Nat Bool := ((children root)[1]?).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × List (Value Nat Bool) × Nat × List Reference
  | .union entry values level free => (entry,values,level,free)
  | _ => (⟨0,.union []⟩,[],0,[])
private def environment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 0 ∨ name = .uninterned 1 then some .empty else none
private theorem actual : built = .done root heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact InternedNestedProvenance.ordinary_available empty 0
  · have same : value = .reference (.uninterned 1) := List.mem_singleton.mp member
    cases same
    exact InternedNestedProvenance.ordinary_available empty 1
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
private theorem firstShape : first = .union (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2 := by cbv
private theorem secondShape : second = .union (fields second).1 (fields second).2.1 (fields second).2.2.1 (fields second).2.2.2 := by cbv
private theorem firstFree : first.free = [.uninterned 0,.uninterned 1] := by cbv
private theorem secondFree : second.free = [] := by cbv
open Language
private theorem open_empty_proof :
    first.free ≠ [] ∧
    ∃ result after outputs middle,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment (fields first).2.1 heap outputs middle ∧ outputs.length = 2 ∧
      result = .empty ∧
      ((result.referenceOf = .empty) ↔ ∀ output ∈ outputs, output.referenceOf = .empty) ∧
      ∀ output ∈ outputs, output.referenceOf = .empty := by
  have sourceAvailable := available.1
  rw [firstShape] at sourceAvailable
  obtain ⟨result,after,outputs,middle,done,calls,kept,_,_,_,growth,_⟩ :=
    SourceCurrentStoredUnionObservations.complete (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2
      environment heap ready sourceAvailable replacements
  have originalDone : InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after := by
    simpa only [←firstShape] using done
  have computed : InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done .empty heap := by cbv
  have resultEmpty := (Outcome.done.inj (originalDone.symm.trans computed)).1
  have called : InternedFreshOrdinaryStoredSubstitution.execute first environment after = .done result after :=
    InternedFreshOrdinaryReplay.build_replay _ _ heap after result after
      ready.semantic.1.normal.facts.coherent.valid originalDone (grows_refl _)
  have paired := SourceCurrentStoredCallsReplay.replay calls after ready.semantic.1.normal.facts.coherent.valid growth
  have availableAfter := kept.available _ sourceAvailable
  rw [firstShape] at called
  have emptyIff := SourceCurrentStoredUnionEmpty.warm (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2
    environment after result outputs kept.ready availableAfter
    (fun name value found => kept.available value (replacements name value found)) called paired
  exact ⟨by rw [firstFree]; simp,result,after,outputs,middle,originalDone,calls,
    calls.length.trans (by cbv),resultEmpty,emptyIff,emptyIff.mp (by rw [resultEmpty]; rfl)⟩
/-- A source-built open union completes both original substitutions and derives a physically empty result. -/
theorem open_empty :
    first.free ≠ [] ∧
    ∃ result after outputs middle,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment (fields first).2.1 heap outputs middle ∧ outputs.length = 2 ∧
      result = .empty ∧
      ((result.referenceOf = .empty) ↔ ∀ output ∈ outputs, output.referenceOf = .empty) ∧
      ∀ output ∈ outputs, output.referenceOf = .empty := open_empty_proof
private theorem closed_flatten_proof :
    ∃ outputs flattened,
      InternedFreshOrdinaryStoredSubstitution.execute second environment heap = .done second heap ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment heap = .done output heap)
        (fields second).2.1 outputs ∧ outputs.length = 2 ∧
      (second.referenceOf = .empty ↔ ∀ output ∈ outputs, output.referenceOf = .empty) ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment heap = .done output heap)
        ([second,.empty,second].flatMap unionMembers) flattened ∧
      ((∀ output ∈ [second,.empty,second], output.referenceOf = .empty) ↔
        ∀ output ∈ flattened, output.referenceOf = .empty) ∧
      ∀ depth view, Same depth view [second,.empty,second] flattened := by
  have sourceAvailable := available.2
  rw [secondShape] at sourceAvailable
  obtain ⟨result,after,outputs,middle,done,calls,_,_,_,_,growth,_⟩ :=
    SourceCurrentStoredUnionObservations.complete (fields second).1 (fields second).2.1 (fields second).2.2.1 (fields second).2.2.2
      environment heap ready sourceAvailable replacements
  have closed := SourceCurrentStoredUnionObservations.closed second environment heap secondFree
  have doneOriginal : InternedFreshOrdinaryStoredSubstitution.execute second environment heap = .done result after := by
    simpa only [←secondShape] using done
  have equal := Outcome.done.inj (doneOriginal.symm.trans closed)
  have called : InternedFreshOrdinaryStoredSubstitution.execute
      (.union (fields second).1 (fields second).2.1 (fields second).2.2.1 (fields second).2.2.2)
      environment heap = .done second heap := by simpa only [←secondShape] using closed
  have paired := SourceCurrentStoredCallsReplay.replay calls heap ready.semantic.1.normal.facts.coherent.valid
    (by simpa only [equal.2] using growth)
  have emptyIff := SourceCurrentStoredUnionEmpty.warm (fields second).1 (fields second).2.1 (fields second).2.2.1 (fields second).2.2.2
    environment heap second outputs ready sourceAvailable replacements called paired
  have seeds : All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment heap = .done output heap)
      [second,.empty,second] [second,.empty,second] :=
    .cons closed (.cons (SourceCurrentStoredUnionObservations.closed .empty environment heap rfl) (.cons closed .nil))
  have seedAvailable : Values heap [second,.empty,second] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact available.2
    · rcases List.mem_cons.mp member with rfl | member
      · exact InternedProbeProvenance.empty_available heap
      · exact List.mem_singleton.mp member ▸ available.2
  obtain ⟨flattened,flatCalls,flatEmpty,observed⟩ := SourceCurrentStoredUnionEmpty.flatten_warm
    [second,.empty,second] [second,.empty,second] environment heap ready seedAvailable replacements seeds
  exact ⟨outputs,flattened,closed,paired,calls.length.trans (by cbv),emptyIff,flatCalls,flatEmpty,observed⟩
/-- A closed source union with a productive Mu retains physical emptiness through repeated member flattening. -/
theorem closed_flatten :
    ∃ outputs flattened,
      InternedFreshOrdinaryStoredSubstitution.execute second environment heap = .done second heap ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment heap = .done output heap)
        (fields second).2.1 outputs ∧ outputs.length = 2 ∧
      (second.referenceOf = .empty ↔ ∀ output ∈ outputs, output.referenceOf = .empty) ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment heap = .done output heap)
        ([second,.empty,second].flatMap unionMembers) flattened ∧
      ((∀ output ∈ [second,.empty,second], output.referenceOf = .empty) ↔
        ∀ output ∈ flattened, output.referenceOf = .empty) ∧
      ∀ depth view, Same depth view [second,.empty,second] flattened := closed_flatten_proof
end MicroCFTA.StoredUnionEmptyKernels
#check @MicroCFTA.StoredUnionEmptyKernels.open_empty
#print MicroCFTA.StoredUnionEmptyKernels.open_empty
#print axioms MicroCFTA.StoredUnionEmptyKernels.open_empty
#check @MicroCFTA.StoredUnionEmptyKernels.closed_flatten
#print MicroCFTA.StoredUnionEmptyKernels.closed_flatten
#print axioms MicroCFTA.StoredUnionEmptyKernels.closed_flatten
