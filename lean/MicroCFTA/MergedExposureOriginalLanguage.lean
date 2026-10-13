import MicroCFTA.MergedSourceExposureCoverage
import MicroCFTA.MergedColdGraphTransport

/-!
# Exact exposure of an original cold-cache language

The returned edges accept exactly the original root's finite terms.
The source reader retains its actual unfolding and allocation effects.
-/
namespace MicroCFTA.MergedExposureOriginalLanguage
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open MergedPhysicalWarmup MergedPhysicalLanguage MergedSourceExposure MergedColdReaderFacts Language

/-- A successful cold reader exposes exactly the finite language from before its first effect. -/
theorem nodeEdges_exact [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before value) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : nodeEdges fuel value before = .done edges after)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph before meaning) value term ↔
      ∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts after meaning edge term := by
  have verified := nodeEdges_verified fuel value before facts prepared available
  have factsAfter : Facts after := by simpa only [done, Result.state] using verified.facts
  have growth : InternedConstructorTemplates.Grows before after := by simpa only [done, Result.state] using verified.growth
  have history : Cache.Extends before.nodes.issued after.nodes.issued := by simpa only [done, Result.state] using verified.history
  exact (MergedColdGraphTransport.accepts_stable before after facts factsAfter prepared growth history meaning value available term).trans
    ((MergedSourceExposureCoverage.actual_exact fuel value before facts prepared available edges after done).2 meaning term)

end MicroCFTA.MergedExposureOriginalLanguage
