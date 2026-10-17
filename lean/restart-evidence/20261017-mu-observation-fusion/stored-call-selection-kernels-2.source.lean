import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentStoredCallSelection
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
namespace MicroCFTA.StoredCallSelectionKernels
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
private def selected : List (Value Nat Bool) := originals.reverse ++ originals
private theorem selection_proof :
    ∃ result after outputs middle selectedOutputs reduced,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment originals heap outputs middle ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment after = .done output after)
        selected selectedOutputs ∧
      Calls environment selected after selectedOutputs after ∧ selectedOutputs.length = 6 ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment after = .done output after)
        (distinctNodes selected) reduced ∧
      Calls environment (distinctNodes selected) after reduced after ∧ reduced.length = 3 ∧
      (∀ value, value ∈ reduced ↔ value ∈ outputs) ∧
      ∀ depth view, Same depth view reduced outputs := by
  have sourceAvailable := available.1
  rw [firstShape] at sourceAvailable
  obtain ⟨result,after,outputs,middle,done,calls,kept,_,_,_,growth,_⟩ :=
    SourceCurrentStoredUnionObservations.complete (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2
      environment heap ready sourceAvailable replacements
  rw [←firstShape] at done
  have warm := SourceCurrentStoredCallsReplay.replay calls after ready.semantic.1.normal.facts.coherent.valid growth
  have membership : ∀ value, value ∈ selected ↔ value ∈ originals := by
    intro value
    simp only [selected,List.mem_append,List.mem_reverse,or_self]
  obtain ⟨selectedOutputs,paired,selectedCalls,selectedMembers,observed⟩ :=
    SourceCurrentStoredCallSelection.observations environment after originals outputs selected warm membership
  have selectedAvailable : Values after selected := by
    intro value member
    exact kept.available value (sourceAvailable.children value ((membership value).mp member))
  obtain ⟨reduced,reducedPaired,reducedCalls,reducedMembers⟩ :=
    SourceCurrentStoredCallSelection.distinct environment after selected selectedOutputs
      kept.ready.semantic.1.normal.facts selectedAvailable paired
  refine ⟨result,after,outputs,middle,selectedOutputs,reduced,done,calls,paired,selectedCalls,
    selectedCalls.length.trans (by cbv),reducedPaired,reducedCalls,reducedCalls.length.trans (by cbv),
    fun value => (reducedMembers value).trans (selectedMembers value),?_⟩
  intro depth view
  exact (SourceCurrentOpenObservationLists.of_members depth view reduced selectedOutputs reducedMembers).trans (observed depth view)
/-- Actual Mu-containing member calls survive source reordering, doubling, and physical deduplication at their warm heap. -/
theorem selection :
    ∃ result after outputs middle selectedOutputs reduced,
      InternedFreshOrdinaryStoredSubstitution.execute first environment heap = .done result after ∧
      Calls environment originals heap outputs middle ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment after = .done output after)
        selected selectedOutputs ∧
      Calls environment selected after selectedOutputs after ∧ selectedOutputs.length = 6 ∧
      All₂ (fun original output => InternedFreshOrdinaryStoredSubstitution.execute original environment after = .done output after)
        (distinctNodes selected) reduced ∧
      Calls environment (distinctNodes selected) after reduced after ∧ reduced.length = 3 ∧
      (∀ value, value ∈ reduced ↔ value ∈ outputs) ∧
      ∀ depth view, Same depth view reduced outputs := selection_proof
end MicroCFTA.StoredCallSelectionKernels
#check @MicroCFTA.StoredCallSelectionKernels.selection
#print MicroCFTA.StoredCallSelectionKernels.selection
#print axioms MicroCFTA.StoredCallSelectionKernels.selection
