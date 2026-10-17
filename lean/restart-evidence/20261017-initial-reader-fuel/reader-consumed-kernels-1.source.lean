import MicroCFTA.SourceCurrentAllocatedReaderConsumed
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.ReaderConsumedIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceCurrentAllocatedReaderConsumed
open MergedFreshOrdinaryExposure (collect)

private def expression : Syntax Nat Bool :=
  .binder false (.union [
    .node [.mk 0 true []],
    .binder false (.union [.node [.mk 1 false []], .node [.mk 2 true [.var 1]]])])

private theorem observed : match InternedFreshOrdinaryConstruction.build expression [] empty with
    | .pending .. => False
    | .done input source =>
      ∃ rows after, collect 20 source [] [input] = .done rows after ∧ rows ≠ [] ∧
        source.nodes.next < after.nodes.next := by
  set_option cbv.maxSteps 300000000 in cbv
  exact ⟨_, _, rfl, by decide, by decide⟩

/-- A literal nested recursive source creates new records and retains every consumed successor. -/
theorem constructed_nested :
    ∃ input source rows after count finalSeen,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      collect 20 source [] [input] = .done rows after ∧ rows ≠ [] ∧
      source.nodes.next < after.nodes.next ∧ count ≤ 20 ∧
      Run count ⟨source, [], [input]⟩ rows ⟨after, finalSeen, []⟩ ∧
      collect count source [] [input] = .done rows after ∧
      collect (count + 13) source [] [input] = .done rows after := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have shape := observed
  rw [built] at shape
  obtain ⟨rows, after, done, nonempty, created⟩ := shape
  obtain ⟨count, finalSeen, enough, actual⟩ := extract 20 source [] [input] rows after done
  exact ⟨input, source, rows, after, count, finalSeen, built, done, nonempty, created, enough,
    actual, actual.exact, actual.stable (count + 13) (by omega)⟩

/-- The same actual source replays its rows at the reached heap without any new cache effect. -/
theorem constructed_warm :
    ∃ input source rows after coldCount warmCount coldSeen warmSeen,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      rows ≠ [] ∧ source.nodes.next < after.nodes.next ∧
      Run coldCount ⟨source, [], [input]⟩ rows ⟨after, coldSeen, []⟩ ∧
      Run warmCount ⟨after, [], [input]⟩ rows ⟨after, warmSeen, []⟩ ∧
      warmCount ≤ 20 ∧ collect warmCount after [] [input] = .done rows after := by
  obtain ⟨input, source, rows, after, count, finalSeen, built, done, nonempty, created,
    _enough, actual, _exact, _padded⟩ := constructed_nested
  have checked := InternedFreshOrdinaryFacts.build_verified expression [] empty InternedNestedFacts.empty_facts
    (by simp [InternedNestedProvenance.Values])
  have valid : InternedShallowHeap.Valid source := by
    simpa only [built, Outcome.state] using checked.facts.coherent.valid
  have warm := MergedFreshOrdinaryColdReplay.collect_replay 20 source after valid [] [input]
    rows after done (grows_refl _)
  obtain ⟨warmCount, warmSeen, enough, warmRun⟩ := extract 20 after [] [input] rows after warm
  exact ⟨input, source, rows, after, count, warmCount, finalSeen, warmSeen,
    built, nonempty, created, actual, warmRun, enough, warmRun.exact⟩

end MicroCFTA.ReaderConsumedIntegration

#print axioms MicroCFTA.ReaderConsumedIntegration.constructed_nested
#check @MicroCFTA.ReaderConsumedIntegration.constructed_nested
#print axioms MicroCFTA.ReaderConsumedIntegration.constructed_warm
#check @MicroCFTA.ReaderConsumedIntegration.constructed_warm
