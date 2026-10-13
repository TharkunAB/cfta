import MicroCFTA.MergedComparisonSoundness
import MicroCFTA.MergedColdGraphTransport

/-!
# Comparison soundness for original cold-cache languages

Both original operand languages remain unchanged by the comparison's
cache effects. A successful comparison therefore proves inclusion before
it starts, as well as in its actual returned cache.
-/
namespace MicroCFTA.MergedComparisonOriginalLanguage
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open MergedPhysicalWarmup MergedPhysicalLanguage MergedSourceComparison MergedComparisonFacts Language

/-- A true comparison result includes the original narrow language in the original wide language. -/
theorem check_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (fuel : Nat) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (after : State Symbol Guard) (done : check clear fuel [] wide narrow state = .done true after)
    (term : Term Symbol) (accepted : EpsilonUnion.Accepts (graph state meaning) narrow term) :
    EpsilonUnion.Accepts (graph state meaning) wide term := by
  have effect := (check_verified clear fuel [] wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed).effect done
  have narrowSame := MergedColdGraphTransport.accepts_stable state after facts effect.facts prepared effect.growth effect.history meaning narrow narrowInput term
  have wideSame := MergedColdGraphTransport.accepts_stable state after facts effect.facts prepared effect.growth effect.history meaning wide wideInput term
  exact wideSame.mpr (MergedComparisonSoundness.check_sound state facts prepared clear meaning clearTrue fuel wide narrow
    wideInput narrowInput wideClosed narrowClosed after done term (narrowSame.mp accepted))

end MicroCFTA.MergedComparisonOriginalLanguage
