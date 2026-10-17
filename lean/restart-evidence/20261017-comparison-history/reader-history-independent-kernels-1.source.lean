import MicroCFTA.SourceCurrentAllocatedReaderHistory
import MicroCFTA.SourceCurrentAllocatedRowReadNumeric
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.ReaderHistoryIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedUnfoldHistory (History Fits heapBound)
open SourceCurrentAllocatedRowReadNumeric (readFuel)
open MergedFreshOrdinaryExposure (nodeEdges)
local notation "initialMass" => InternedValueMassHeap.initialBound

private def productive : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [], .mk 1 false [.var 0]])

private def unionSource : Syntax Nat Bool := .union [productive, .node [.mk 3 false []]]

private theorem own_histories (expression : Syntax Nat Bool) :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source)) input source = .done rows after ∧
      History source after ∧
      Fits (heapBound source.nodes.next source.edges.next (initialMass source)) after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source)) input after = .done rows after ∧
      History after after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source) + 23) input after = .done rows after := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input source built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input source built
  have stored := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  obtain ⟨rows, after, done, _graph, keeps, afterSemantic, _afterStored, _nodes, _edges, _resident, _closed, _stable⟩ :=
    SourceCurrentAllocatedRowReadNumeric.complete input source (initialMass source) semantic available closed stored
  have actual := SourceCurrentAllocatedReaderHistory.nodeEdges_history
    (initialMass source) (readFuel source.nodes.next source.edges.next (initialMass source)) input source semantic
    (InternedValueMassBinderDepth.stored_bounded source _ stored) available closed rows after done
  have bounded := actual.complete semantic.ready.semantic semantic.ready.covered semantic.ready.depth stored
  have warm := MergedFreshOrdinaryColdReplay.nodeEdges_replay
    (readFuel source.nodes.next source.edges.next (initialMass source)) input source after
    semantic.ready.semantic.1.normal.facts.coherent.valid rows after done (grows_refl _)
  have warmHistory := SourceCurrentAllocatedReaderHistory.nodeEdges_history
    (initialMass source) (readFuel source.nodes.next source.edges.next (initialMass source)) input after afterSemantic
    bounded.1.bounded (keeps.available input available) closed rows after warm
  have all := actual.trans warmHistory
  have originalCeiling := all.complete semantic.ready.semantic semantic.ready.covered semantic.ready.depth stored
  have padded := MergedFreshOrdinaryColdReplay.nodeEdges_replay_stable
    (readFuel source.nodes.next source.edges.next (initialMass source)) 23 input source after
    semantic.ready.semantic.1.normal.facts.coherent.valid rows after done (grows_refl _)
  exact ⟨input, source, rows, after, built, done, actual, originalCeiling.2, warm, warmHistory, padded⟩

private theorem mu_shape : match InternedFreshOrdinaryConstruction.build productive [] empty with
    | .pending .. => False
    | .done input _ => ∃ entry body depth ordinary, input = .mu entry body depth ordinary := by
  set_option cbv.maxSteps 100000000 in cbv
  exact ⟨_, _, _, _, rfl⟩

/-- The own computed Mu read and exact warm read extract histories at their actual heaps. -/
theorem constructed_mu :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build productive [] empty = .done input source ∧
      (∃ entry body depth ordinary, input = .mu entry body depth ordinary) ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source)) input source = .done rows after ∧
      History source after ∧
      Fits (heapBound source.nodes.next source.edges.next (initialMass source)) after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source)) input after = .done rows after ∧
      History after after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source) + 23) input after = .done rows after := by
  obtain ⟨input, source, rows, after, built, rest⟩ := own_histories productive
  have shape := mu_shape
  rw [built] at shape
  exact ⟨input, source, rows, after, built, shape, rest⟩

private theorem union_shape : match InternedFreshOrdinaryConstruction.build unionSource [] empty with
    | .pending .. => False
    | .done input _ => ∃ entry members depth free, input = .union entry members depth free ∧
        ∃ member ∈ members, ∃ muEntry body level ordinary, member = .mu muEntry body level ordinary := by
  set_option cbv.maxSteps 100000000 in cbv
  exact ⟨_, _, _, _, rfl, _, .head _, _, _, _, _, rfl⟩

/-- A real union closure extracts its own cold and warm histories with one original ceiling. -/
theorem constructed_union :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build unionSource [] empty = .done input source ∧
      (∃ entry members depth free, input = .union entry members depth free ∧
        ∃ member ∈ members, ∃ muEntry body level ordinary, member = .mu muEntry body level ordinary) ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source)) input source = .done rows after ∧
      History source after ∧
      Fits (heapBound source.nodes.next source.edges.next (initialMass source)) after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source)) input after = .done rows after ∧
      History after after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialMass source) + 23) input after = .done rows after := by
  obtain ⟨input, source, rows, after, built, rest⟩ := own_histories unionSource
  have shape := union_shape
  rw [built] at shape
  exact ⟨input, source, rows, after, built, shape, rest⟩

end MicroCFTA.ReaderHistoryIntegration

#print axioms MicroCFTA.ReaderHistoryIntegration.constructed_mu
#check @MicroCFTA.ReaderHistoryIntegration.constructed_mu
#print axioms MicroCFTA.ReaderHistoryIntegration.constructed_union
#check @MicroCFTA.ReaderHistoryIntegration.constructed_union
