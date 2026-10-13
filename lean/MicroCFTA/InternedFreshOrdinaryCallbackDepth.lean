import MicroCFTA.InternedNormalizationDepthExact
import MicroCFTA.InternedFreshOrdinaryNormal

/-!
# Exact depth of a repaired source callback

The callback executes its source body and removes root self alternatives.
The filter preserves the complete body's cached depth. This result does
not identify the depths of body executions under different arguments.
-/
namespace MicroCFTA.InternedFreshOrdinaryCallbackDepth
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryNormal
open InternedBinderProtocol (Reference)

/-- A completed callback exposes its actual source body and preserves that body's depth. -/
theorem callback_depth [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback expression environment name state = .done value after) :
    ∃ body beforeFilter, build expression (.reference name :: environment) state = .done body beforeFilter ∧
      value.depth = body.depth := by
  have verified := build_verified expression _ state normal.facts inputs
  have retained := build_normal expression _ state normal inputs
  unfold callback at done
  cases computed : build expression (.reference name :: environment) state with
  | pending key stopped => simp only [computed, Outcome.bind] at done; cases done
  | done body beforeFilter =>
      have beforeNormal : Normal beforeFilter := by simpa only [computed, Outcome.state] using retained
      have available := verified.result body beforeFilter computed
      simp only [computed, Outcome.bind, work, Outcome.done.injEq] at done
      refine ⟨body, beforeFilter, rfl, ?_⟩
      rw [← done.1]
      exact InternedNormalizationDepthExact.filter_depth name body beforeFilter
        beforeNormal.facts.coherent beforeNormal.facts.cached beforeNormal.facts.linked beforeNormal.live available

end MicroCFTA.InternedFreshOrdinaryCallbackDepth
