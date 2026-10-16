import MicroCFTA.EndpointStatefulGateCompletion
import MicroCFTA.SourceCurrentSecondaryCompletion
import MicroCFTA.SourcePrimaryGateEffects
import MicroCFTA.SourceCurrentSecondaryEffects

/-!
# Finite current class gates from physical readiness

Semantic readiness contains the complete empty-environment source context,
decoded depth heap, and record coverage. The separate cost heap supplies
the last ranked-gate field. These facts construct the certified gate input.
No source construction equation or completed gate trace is a premise.

Both current modes retain the exact returned constructor heap and ordered
short circuits. The predicates are pure Boolean inputs here. Their source
memo calls, pending publication, and runtime forcing remain separate.
-/
namespace MicroCFTA.SourceCurrentClassGateCompletion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open EqualityNormalize
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Existing semantic fields and weighted costs supply every ranked-gate heap premise. -/
theorem gate_ready {before : State Symbol Guard} (semantic : SemanticReady before)
    (costs : CostHeap before) : InternedFreshOrdinaryMemoGateTrace.Ready before :=
  ⟨semantic.ready.semantic.1, semantic.ready.semantic.2, semantic.ready.covered, costs⟩

/-- An available record in a ready heap supplies the actual certified gate input. -/
def node_of_ready (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (value : Value Symbol Guard) (available : Available before value) :
    InternedFreshOrdinaryGateRank.Node Symbol Guard :=
  (gate_ready semantic costs).node value available

/-- Initial physical invariants derive finite primary execution and its actual ordered trace. -/
theorem primary_class_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : Class) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) :
    ∃ bound answer final,
      EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before answer final ∧
      SemanticReady final ∧ CostHeap final ∧ Keeps before final ∧ Values final values ∧
      ∀ extra, SourceCurrentMuEndpoint.classMeets true unconstrained reaches (bound + extra)
        values paths before = .done (some answer) final := by
  have emptyAvailable : Available before (.empty : Value Symbol Guard) := empty_available before
  let input := node_of_ready before semantic costs .empty emptyAvailable
  obtain ⟨bound, answer, final, _, _, stable⟩ := EndpointStatefulGateCompletion.class_eventually_exact
    unconstrained reaches input values available paths
  have actual := stable 0
  rw [Nat.add_zero] at actual
  have trace := EndpointStatefulGateTrace.class_trace_of_done unconstrained reaches bound values paths
    before answer final.state actual
  have effects := SourcePrimaryGateEffects.class_effects (fun _ => True) unconstrained reaches trace
    semantic costs available (by intro key edge found; trivial)
  exact ⟨bound, answer, final.state, trace, effects.1, effects.2.2.1, effects.2.1,
    fun value member => effects.2.1.available value (available value member),
    fun extra => by simpa only [SourceCurrentMuEndpoint.primary_class, input, node_of_ready,
      InternedFreshOrdinaryMemoGateTrace.Ready.node] using stable extra⟩

/-- Initial physical invariants derive finite execution of the changed secondary endpoint policy. -/
theorem secondary_class_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : Class) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) :
    ∃ bound answer final,
      SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before answer final ∧
      SemanticReady final ∧ CostHeap final ∧ Keeps before final ∧ Values final values ∧
      ∀ extra, SourceCurrentMuEndpoint.classMeets false unconstrained reaches (bound + extra)
        values paths before = .done (some answer) final := by
  have emptyAvailable : Available before (.empty : Value Symbol Guard) := empty_available before
  let input := node_of_ready before semantic costs .empty emptyAvailable
  obtain ⟨bound, answer, final, _, _, stable⟩ := SourceCurrentSecondaryCompletion.class_eventually_exact
    unconstrained input values available paths
  have actual := stable 0
  rw [Nat.add_zero] at actual
  have trace := SourceCurrentSecondaryTrace.class_trace_of_done unconstrained bound values paths
    before answer final.state actual
  have effects := SourceCurrentSecondaryEffects.class_effects (fun _ => True) unconstrained trace
    semantic costs available (by intro key edge found; trivial)
  exact ⟨bound, answer, final.state, trace, effects.1, effects.2.2.1, effects.2.1,
    fun value member => effects.2.1.available value (available value member),
    fun extra => by simpa only [SourceCurrentSecondaryTrace.actual_current_class_eq, input, node_of_ready,
      InternedFreshOrdinaryMemoGateTrace.Ready.node] using stable extra⟩

end MicroCFTA.SourceCurrentClassGateCompletion
