import MicroCFTA.SourceCurrentStoredNodeExpansion
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

namespace MicroCFTA.StoredNodeExpansionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
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
private theorem firstDone : execute first environment heap = .done first heap := by cbv

/-- A source-built closed parent exposes both rows and exact child calls without rebuilding its parent. -/
theorem closed_nested_mu :
    build expression captures empty = .done root heap ∧ Ready heap ∧ first.free = [] ∧
    (fields first).2.1.length = 2 ∧
    (children first).any (fun value => match value with | .mu .. => true | _ => false) = true ∧
    execute first environment heap = .done first heap ∧
    Expansion environment (fields first).2.1 heap first := by
  have sourceAvailable := available.1
  rw [firstShape] at sourceAvailable
  have warm := firstDone
  rw [firstShape] at warm
  have expanded := SourceCurrentStoredNodeExpansion.node_warm (fields first).1 (fields first).2.1
    (fields first).2.2.1 (fields first).2.2.2 environment heap ready.semantic.1.normal sourceAvailable replacements
    (.node (fields first).1 (fields first).2.1 (fields first).2.2.1 (fields first).2.2.2) warm
  rw [← firstShape] at expanded
  exact ⟨actual,ready,by cbv,by cbv,by cbv,firstDone,expanded⟩

private def changed := execute second environment heap
private def output : Value Nat Bool := match changed with | .done value _ => value | .pending .. => .empty
private theorem changedDone : changed = .done output changed.state := by cbv
private theorem changedKeeps : Keeps heap changed.state ∧ Available changed.state output := by
  obtain ⟨result,after,done,kept,resultAvailable,_⟩ :=
    SourceCurrentStoredReconstruction.execute second environment heap ready available.2 replacements
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (changedDone.symm.trans done)
  exact ⟨kept,resultAvailable⟩

/-- An open two-row parent loses its empty-child row, then every original row replays at the same reached heap. -/
theorem open_dead_row :
    second.free ≠ [] ∧ (fields second).2.1.length = 2 ∧
    execute second environment heap = .done output changed.state ∧
    Keeps heap changed.state ∧ Available changed.state output ∧
    (InternedEdgeResidency.nodeEdges output).length = 1 ∧
    execute second environment changed.state = .done output changed.state ∧
    Expansion environment (fields second).2.1 changed.state output := by
  have done : execute second environment heap = .done output changed.state := changedDone
  have warm := InternedFreshOrdinaryReplay.build_replay
    (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves second) [] second)
    ((InternedStoredSubstitution.leaves second).map (InternedStoredSubstitution.input environment))
    heap changed.state output changed.state ready.semantic.1.normal.facts.coherent.valid done (grows_refl _)
  have sourceAvailable := changedKeeps.1.available second available.2
  rw [secondShape] at sourceAvailable warm
  have expanded := SourceCurrentStoredNodeExpansion.node_warm (fields second).1 (fields second).2.1
    (fields second).2.2.1 (fields second).2.2.2 environment changed.state changedKeeps.1.ready.semantic.1.normal
    sourceAvailable (fun name value found => changedKeeps.1.available value (replacements name value found)) output warm
  rw [← secondShape] at warm
  exact ⟨by cbv; simp, by cbv, done, changedKeeps.1, changedKeeps.2, by cbv, warm, expanded⟩

end MicroCFTA.StoredNodeExpansionKernels
