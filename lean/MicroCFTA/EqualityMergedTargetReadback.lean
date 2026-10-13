import MicroCFTA.MergedNormalReadback

/-!
# Transfer of exact ordinary constructor readback

Exact node reconstruction depends on the complete immutable value and
its resident edge records. A second coherent cache that contains the same
complete value therefore replays the same request. No cache-growth premise
is required for this transfer.
-/
namespace MicroCFTA.EqualityMergedTargetReadback
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedEdgeResidency EqualityOrdinaryReadback

/-- An exact ordinary readback transfers to every coherent cache that retains the same complete value. -/
theorem normal_transfer [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (beforeFacts : Facts before) (afterFacts : Facts after)
    (value : Value Symbol Guard) (beforeAvailable : Available before value) (afterAvailable : Available after value)
    (normal : Normal before value) : Normal after value :=
  MergedNormalReadback.normal_transfer before after beforeFacts afterFacts.coherent value beforeAvailable afterAvailable normal

/-- A complete immutable value has at least one verified exact constructor readback. -/
def Replayable [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) : Prop :=
  ∃ state, Facts state ∧ Available state value ∧ Normal state value

/-- Any later available copy of a replayable ordinary value reconstructs without effects. -/
theorem replayable_normal [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (replayable : Replayable value)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value) : Normal state value := by
  obtain ⟨before, beforeFacts, beforeAvailable, normal⟩ := replayable
  exact normal_transfer before state beforeFacts facts value beforeAvailable available normal

end MicroCFTA.EqualityMergedTargetReadback
