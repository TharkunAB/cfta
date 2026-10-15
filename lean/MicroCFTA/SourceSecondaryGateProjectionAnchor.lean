import MicroCFTA.SourceSecondaryGateReplay
import MicroCFTA.InternedSourceGateReplay
import MicroCFTA.SourceSecondaryGateEndpointClosed
import MicroCFTA.SourceSecondaryGateProjectionSupport

/-!
# Ready anchors after clear secondary gate traces

The actual completed gate retains the semantic and weighted source heaps.
Its final cache supplies an anchor with the original inputs still available
and the same false query without a constructor effect. Later projection
caches can use the semantic replay laws. They need not retain a cost heap.
-/
namespace MicroCFTA.SourceSecondaryGateProjectionAnchor
open InternedConstructorTemplates InternedProbeProvenance
open InternedFreshOrdinaryStatefulGateTrace EqualityNormalize
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- A false node trace derives its ready final anchor and exact effect-free false certificate. -/
theorem node_anchor [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {path : Path} {value : Value Symbol Guard} {before final : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before false final)
    (semantic : SemanticReady before) (ready : GateReady before) (available : Available before value) :
    SemanticReady final ∧ GateReady final ∧ Keeps before final ∧ Available final value ∧
      NodeTrace unconstrained path value final false final := by
  have effects := SourceSecondaryGateReplay.node_replay unconstrained path value before false final
    trace semantic available
  have weighted := InternedSourceGateReplay.node_replay unconstrained path value before false final
    trace ready available
  exact ⟨effects.1, weighted.1, effects.2.1, effects.2.1.available value available,
    weighted.2.2.2 final (grows_refl final)⟩

/-- A false path trace derives its ready final anchor and retains every original forest value. -/
theorem path_anchor [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {path : Path} {before final : State Symbol Guard}
    (trace : PathTrace unconstrained values path before false final)
    (semantic : SemanticReady before) (ready : GateReady before)
    (available : ∀ value ∈ values, Available before value) :
    SemanticReady final ∧ GateReady final ∧ Keeps before final ∧
      (∀ value ∈ values, Available final value) ∧ PathTrace unconstrained values path final false final := by
  have effects := SourceSecondaryGateReplay.path_replay unconstrained values path before false final
    trace semantic available
  have weighted := InternedSourceGateReplay.path_replay unconstrained values path before false final
    trace ready available
  exact ⟨effects.1, weighted.1, effects.2.1,
    fun value member => effects.2.1.available value (available value member),
    weighted.2.2.2 final (grows_refl final)⟩

/-- A false class derives one ready anchor and an effect-free false certificate for each original path. -/
theorem class_anchor [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before final : State Symbol Guard}
    (trace : ClassTrace unconstrained values paths before false final)
    (semantic : SemanticReady before) (ready : GateReady before)
    (available : ∀ value ∈ values, Available before value) :
    SemanticReady final ∧ GateReady final ∧ Keeps before final ∧
      (∀ value ∈ values, Available final value) ∧ ClassTrace unconstrained values paths final false final ∧
      ∀ path ∈ paths, PathTrace unconstrained values path final false final := by
  have effects := SourceSecondaryGateReplay.class_replay unconstrained values paths before false final
    trace semantic available
  have weighted := InternedSourceGateReplay.class_replay unconstrained values paths before false final
    trace ready available
  exact ⟨effects.1, weighted.1, effects.2.1,
    fun value member => effects.2.1.available value (available value member),
    weighted.2.2.2 final (grows_refl final),
    SourceSecondaryGateReplay.false_class_paths unconstrained values paths before final
      trace semantic available final (grows_refl final)⟩

/-- Root-path support derives original closedness from the weighted heap at its fixed gate anchor. -/
theorem support_endpoint_closed [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard} {value : Value Symbol Guard}
    (support : SourceSecondaryGateProjectionSupport.Support unconstrained anchor [] value)
    (ready : GateReady anchor) : value.free = [] := by
  rcases support with closed | ⟨available, trace⟩
  · exact closed
  · exact SourceSecondaryGateEndpointClosed.endpoint_closed unconstrained trace ready available

end MicroCFTA.SourceSecondaryGateProjectionAnchor
