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

/-- A literal nested recursive source constructs its own collector and exact consumed path. -/
theorem constructed_nested :
    ∃ input source rows after witnessFuel count finalSeen,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      collect witnessFuel source [] [input] = .done rows after ∧ 0 < count ∧ count ≤ witnessFuel ∧
      Run count ⟨source, [], [input]⟩ rows ⟨after, finalSeen, []⟩ ∧
      collect count source [] [input] = .done rows after ∧
      collect (count + 13) source [] [input] = .done rows after := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input source built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input source built
  obtain ⟨fuel, rows, after, done, _depth, _bounded⟩ :=
    MergedFreshOrdinaryColdTermination.collect_complete _ source semantic.ready.semantic semantic.ready.covered
      semantic.ready.depth (InternedMuDepthInventory.initial_bounded source semantic.ready.semantic.1.normal.facts)
      [] [input] (by intro value member; obtain rfl := List.mem_singleton.mp member; exact available)
      (by intro value member; obtain rfl := List.mem_singleton.mp member; exact closed)
  obtain ⟨count, finalSeen, enough, actual⟩ := extract fuel source [] [input] rows after done
  have positive : 0 < count := by
    cases count with
    | zero => have impossible := actual.exact; cases impossible
    | succ => omega
  exact ⟨input, source, rows, after, fuel, count, finalSeen, built, done, positive, enough,
    actual, actual.exact, actual.stable (count + 13) (by omega)⟩

/-- The exact first returned heap supports a second complete path with no new cache effect. -/
theorem constructed_warm :
    ∃ input source rows after coldCount warmCount coldSeen warmSeen,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      0 < coldCount ∧ 0 < warmCount ∧
      Run coldCount ⟨source, [], [input]⟩ rows ⟨after, coldSeen, []⟩ ∧
      Run warmCount ⟨after, [], [input]⟩ rows ⟨after, warmSeen, []⟩ ∧
      collect warmCount after [] [input] = .done rows after := by
  obtain ⟨input, source, rows, after, fuel, count, finalSeen, built, done, positive,
    _enough, actual, _exact, _padded⟩ := constructed_nested
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have valid : InternedConstructorTemplates.Valid source := by
    simpa only [built, Outcome.state] using checked.facts.coherent.valid
  have warm := MergedFreshOrdinaryColdReplay.collect_replay fuel source after valid [] [input]
    rows after done (grows_refl _)
  obtain ⟨warmCount, warmSeen, _enough, warmRun⟩ := extract fuel after [] [input] rows after warm
  have warmPositive : 0 < warmCount := by
    cases warmCount with
    | zero => have impossible := warmRun.exact; cases impossible
    | succ => omega
  exact ⟨input, source, rows, after, count, warmCount, finalSeen, warmSeen,
    built, positive, warmPositive, actual, warmRun, warmRun.exact⟩

end MicroCFTA.ReaderConsumedIntegration

#print axioms MicroCFTA.ReaderConsumedIntegration.constructed_nested
#check @MicroCFTA.ReaderConsumedIntegration.constructed_nested
#print axioms MicroCFTA.ReaderConsumedIntegration.constructed_warm
#check @MicroCFTA.ReaderConsumedIntegration.constructed_warm
