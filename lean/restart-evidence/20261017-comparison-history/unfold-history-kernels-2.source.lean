import MicroCFTA.SourceCurrentAllocatedUnfoldHistory
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

namespace MicroCFTA.UnfoldHistoryIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceCurrentAllocatedUnfoldHistory
open InternedFreshOrdinaryStoredSubstitution (unfold)
local notation "initialMass" => InternedValueMassHeap.initialBound

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [], .mk 1 false [.var 0]])

private theorem literal_changes : match InternedFreshOrdinaryConstruction.build expression [] empty with
    | .pending .. => False
    | .done input source => match unfold input source with
      | .pending .. => False
      | .done _ after => source.nodes.next < after.nodes.next := by
  set_option cbv.maxSteps 100000000 in cbv

/-- A source-built productive Mu creates an actual changing event and its initial-only heap bound. -/
theorem constructed_change :
    ∃ input source result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      unfold input source = .done result after ∧ source.nodes.next < after.nodes.next ∧
      Event source after ∧ History source after ∧
      Good (initialMass source) after ∧
      Fits (heapBound source.nodes.next source.edges.next (initialMass source)) after ∧
      HeightOrder.VectorBelow (initialMass source) (measure (initialMass source) after) (measure (initialMass source) source) := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input source built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input source built
  have stored := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  obtain ⟨result, after, done, _context, _cached, _covered, _output, _growth, _history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded input source semantic.ready.semantic.1
      available semantic.ready.semantic.2 semantic.ready.covered
  have changes : source.nodes.next < after.nodes.next := by
    simpa only [built, done] using literal_changes
  have event : Event source after := .unfold input result available closed done
  have actual : History source after := .step event (.refl after)
  have bounded := actual.complete semantic.ready.semantic semantic.ready.covered semantic.ready.depth stored
  have initialGood : Good (initialMass source) source := ⟨semantic.ready.semantic, semantic.ready.covered,
    semantic.ready.depth, InternedValueMassBinderDepth.stored_bounded source _ stored,
    (by intro item member; cases member), (by intro item member; cases member)⟩
  have strict := event.progress initialGood
  rcases strict with decrease | same
  · exact ⟨input, source, result, after, built, done, changes, event, actual, bounded.1, bounded.2, decrease⟩
  · subst after
    omega

private theorem repeated {heap : State Nat Bool} (event : Event heap heap) (count : Nat) : History heap heap := by
  induction count with
  | zero => exact .refl heap
  | succ count ih => exact .step event ih

/-- Any number of exact warm replays retains the same original-source resource ceiling. -/
theorem arbitrary_warm_suffix (count : Nat) :
    ∃ input source result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      unfold input source = .done result after ∧ source.nodes.next < after.nodes.next ∧
      (∀ index, index < count → unfold input after = .done result after) ∧
      Event after after ∧ History after after ∧ History source after ∧
      Good (initialMass source) after ∧
      Fits (heapBound source.nodes.next source.edges.next (initialMass source)) after := by
  obtain ⟨input, source, result, after, built, done, changes, _event, first, _good, _fits, _strict⟩ := constructed_change
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input source built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input source built
  have stored := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  obtain ⟨produced, final, completed, _context, _cached, _covered, _output, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded input source semantic.ready.semantic.1
      available semantic.ready.semantic.2 semantic.ready.covered
  have equal := Outcome.done.inj (done.symm.trans completed)
  rcases equal with ⟨sameResult, sameHeap⟩
  subst produced
  subst final
  have warm := InternedFreshOrdinaryStoredSubstitution.unfold_replay input source after result after
    semantic.ready.semantic.1.normal.facts.coherent.valid done (grows_refl _)
  have event : Event after after := .unfold input result (available.grows source after growth history) closed warm
  have tail := repeated event count
  have whole := first.trans tail
  have bounded := whole.complete semantic.ready.semantic semantic.ready.covered semantic.ready.depth stored
  exact ⟨input, source, result, after, built, done, changes, fun _ _ => warm,
    event, tail, whole, bounded⟩

end MicroCFTA.UnfoldHistoryIntegration

#print axioms MicroCFTA.UnfoldHistoryIntegration.constructed_change
#check @MicroCFTA.UnfoldHistoryIntegration.constructed_change
#print axioms MicroCFTA.UnfoldHistoryIntegration.arbitrary_warm_suffix
#check @MicroCFTA.UnfoldHistoryIntegration.arbitrary_warm_suffix
