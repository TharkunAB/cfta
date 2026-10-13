import MicroCFTA.InternedFreshOrdinaryFirstOrderHeap
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.MergedSourceExposureCoverage
import MicroCFTA.MergedColdGraphTransport

/-!
# Finite exact Mu and union exposure after repaired source construction

An arbitrary binder-free body supplies its actual completed source cache.
The stored-body preparation and closed-root premises are derived from that
run. Actual cold exposure then finishes with resident closed edges, exact
cache histories, stable extra fuel, and the original physical language.
-/
namespace MicroCFTA.SourceFirstOrderExposure
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance InternedShallowHeap InternedStoredShallowCompletion
open MergedPhysicalWarmup MergedSourceExposureLanguage
open Language

/-- Arbitrary first-order source bodies produce finite exact cold rows without prepared-input premises. -/
theorem source_read [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : BinderFree body) :
    ∃ value before fuel edges after,
      InternedFreshOrdinaryConstruction.build (.binder smart body) [] empty = .done value before ∧
      Facts before ∧ Prepared before ∧ Available before value ∧ value.free = [] ∧
      MergedSourceExposure.nodeEdges fuel value before = .done edges after ∧
      Facts after ∧ Prepared after ∧ Grows before after ∧
      Cache.Extends before.nodes.issued after.nodes.issued ∧ NoNewMu before after ∧
      Edges after edges ∧ MergedColdReaderClosedInputs.ClosedEdges edges ∧
      (∀ extra, MergedSourceExposure.nodeEdges (fuel + extra) value before = .done edges after) ∧
      (∀ edge, edge ∈ edges ↔ Origin after [value] edge) ∧
      (∀ meaning term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph before meaning) value term ↔
        ∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts after meaning edge term) := by
  obtain ⟨value, before, built, beforeFacts, available, prepared⟩ :=
    InternedFreshOrdinaryFirstOrderHeap.closed_prepared smart body free
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty (.binder smart body) value before built
  obtain ⟨fuel, edges, after, read, afterFacts, afterPrepared, growth, history, unchanged, resident, children, stable⟩ :=
    MergedColdReaderFacts.read_closed value before beforeFacts prepared available closed
  have exactRows := MergedSourceExposureCoverage.actual_exact fuel value before beforeFacts prepared available edges after read
  refine ⟨value, before, fuel, edges, after, built, beforeFacts, prepared, available, closed,
    read, afterFacts, afterPrepared, growth, history, unchanged, resident, children, stable, exactRows.1, ?_⟩
  intro meaning term
  exact (MergedColdGraphTransport.accepts_stable before after beforeFacts afterFacts prepared growth history
    meaning value available term).trans (exactRows.2 meaning term)

end MicroCFTA.SourceFirstOrderExposure
