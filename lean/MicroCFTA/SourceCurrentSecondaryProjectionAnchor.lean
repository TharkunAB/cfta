import MicroCFTA.SourceCurrentSecondaryReplay
import MicroCFTA.InternedFreshOrdinaryMemoGateClasses
import MicroCFTA.SourceCurrentSecondaryProjectionSupport

/-!
# Exact gate replay in caches that retain all completed constructor work

A completed source graph can run in any cache that extends its final cache.
Each original unfolding then reuses its exact stored result. The replay has
the same Boolean and no constructor-cache effect. This is a derived growth
law, not an observation premise for the whole gate.
-/
namespace MicroCFTA.SourceCurrentSecondaryProjectionAnchor.Weighted
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryGateRank (step)
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
open SourceCurrentSecondaryTrace EqualityNormalize

/-- Every completed node graph retains its source invariants and replays exactly above its final cache. -/
theorem node_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : NodeTrace unconstrained path value state answer final)
    (ready : Ready state) (available : Available state value) :
    Ready final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      ∀ target, Grows final target → NodeTrace unconstrained path value target answer target := by
  revert available ready
  induction trace using NodeTrace.rec
      (motive_2 := fun values index path state answer final _ => Ready state →
        (∀ value ∈ values, Available state value) →
          Ready final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
            ∀ target, Grows final target → ChildTrace unconstrained values index path target answer target)
      (motive_3 := fun index path edges state answer final _ => Ready state →
        (∀ value ∈ edges.flatMap EdgeValue.children, Available state value) →
          Ready final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
            ∀ target, Grows final target → EdgesTrace unconstrained index path edges target answer target) with
  | empty => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .empty⟩
  | reference => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .reference⟩
  | union members => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .union members⟩
  | finite fast => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .finite fast⟩
  | endpoint slow => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .endpoint slow⟩
  | branches slow trace ih =>
      intro ready available
      obtain ⟨finalReady, growth, history, replay⟩ := ih ready (fun value member => available.children value member)
      exact ⟨finalReady, growth, history, fun target grows => .branches slow (replay target grows)⟩
  | constrained blocked => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .constrained blocked⟩
  | closed plain closed => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .closed plain closed⟩
  | unfold plain opened actual trace ih =>
      intro ready available
      let node := ready.node _ available
      let after := (step node).result
      have fields := Outcome.done.inj ((step node).actual.symm.trans actual)
      have valueEqual := fields.1
      have stateEqual := fields.2
      have afterReady := stateEqual ▸ node_ready after
      have afterAvailable := stateEqual ▸ (valueEqual ▸ after.available)
      obtain ⟨finalReady, growth, history, replay⟩ := ih afterReady afterAvailable
      have first := InternedFreshOrdinaryStatefulGateCompletion.step_growth node
      have firstGrowth := stateEqual ▸ first.1
      have firstHistory := stateEqual ▸ first.2
      refine ⟨finalReady, grows_trans firstGrowth growth, extends_trans firstHistory history, ?_⟩
      intro target retained
      exact .unfold plain opened
        (InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ target _ _ ready.1.normal.facts.coherent.valid actual
          (grows_trans growth retained)) (replay target retained)
  | missing absent ready available => exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .missing absent⟩
  | present found trace ih ready available =>
      obtain ⟨finalReady, growth, history, replay⟩ := ih ready (available _ (List.mem_of_getElem? found))
      exact ⟨finalReady, growth, history, fun target retained => .present found (replay target retained)⟩
  | nil ready available => exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .nil⟩
  | stop head ih ready available =>
      obtain ⟨finalReady, growth, history, replay⟩ := ih ready (fun value member => available value (by simp [member]))
      exact ⟨finalReady, growth, history, fun target grows => .stop (replay target grows)⟩
  | next head tail headIH tailIH ready available =>
      obtain ⟨middleReady, firstGrowth, firstHistory, firstReplay⟩ := headIH ready
        (fun value member => available value (by simp [member]))
      obtain ⟨finalReady, growth, history, replay⟩ := tailIH middleReady
        (fun value member => (available value (by simp [member])).grows _ _ firstGrowth firstHistory)
      exact ⟨finalReady, grows_trans firstGrowth growth, extends_trans firstHistory history,
        fun target retained => .next (firstReplay target (grows_trans growth retained)) (replay target retained)⟩

/-- Complete source paths replay in every cache that retains their completed constructor work. -/
theorem path_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : PathTrace unconstrained values path state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value) :
    Ready final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      ∀ target, Grows final target → PathTrace unconstrained values path target answer target := by
  cases trace with
  | empty => exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .empty⟩
  | child trace =>
      cases trace with
      | missing absent => exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .child (.missing absent)⟩
      | present found trace =>
          obtain ⟨finalReady, growth, history, replay⟩ := node_replay _ _ _ _ _ _ trace ready (available _ (List.mem_of_getElem? found))
          exact ⟨finalReady, growth, history, fun target retained => .child (.present found (replay target retained))⟩

/-- A complete class replays its exact Boolean without a cache effect above its completed final cache. -/
theorem class_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : ClassTrace unconstrained values paths state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value) :
    Ready final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      ∀ target, Grows final target → ClassTrace unconstrained values paths target answer target := by
  revert available ready
  induction trace with
  | nil => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, fun _ _ => .nil⟩
  | stop head =>
      intro ready available
      obtain ⟨finalReady, growth, history, replay⟩ := path_replay _ _ _ _ _ _ head ready available
      exact ⟨finalReady, growth, history, fun target retained => .stop (replay target retained)⟩
  | next head tail ih =>
      intro ready available
      obtain ⟨middleReady, firstGrowth, firstHistory, firstReplay⟩ := path_replay _ _ _ _ _ _ head ready available
      obtain ⟨finalReady, growth, history, replay⟩ := ih middleReady
        (fun value member => (available value member).grows _ _ firstGrowth firstHistory)
      exact ⟨finalReady, grows_trans firstGrowth growth, extends_trans firstHistory history,
        fun target retained => .next (firstReplay target (grows_trans growth retained)) (replay target retained)⟩

end MicroCFTA.SourceCurrentSecondaryProjectionAnchor.Weighted

namespace MicroCFTA.SourceCurrentSecondaryProjectionAnchor
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentSecondaryTrace EqualityNormalize
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
  have effects := SourceCurrentSecondaryReplay.node_replay unconstrained path value before false final
    trace semantic available
  have weighted := Weighted.node_replay unconstrained path value before false final
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
  have effects := SourceCurrentSecondaryReplay.path_replay unconstrained values path before false final
    trace semantic available
  have weighted := Weighted.path_replay unconstrained values path before false final
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
  have effects := SourceCurrentSecondaryReplay.class_replay unconstrained values paths before false final
    trace semantic available
  have weighted := Weighted.class_replay unconstrained values paths before false final
    trace ready available
  exact ⟨effects.1, weighted.1, effects.2.1,
    fun value member => effects.2.1.available value (available value member),
    weighted.2.2.2 final (grows_refl final),
    SourceCurrentSecondaryReplay.false_class_paths unconstrained values paths before final
      trace semantic available final (grows_refl final)⟩

/-- Root-path support derives original closedness from the weighted heap at its fixed gate anchor. -/
theorem support_endpoint_closed [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard} {value : Value Symbol Guard}
    (support : SourceCurrentSecondaryProjectionSupport.Support unconstrained anchor [] value)
    (ready : GateReady anchor) : value.free = [] := by
  rcases support with closed | ⟨available, trace⟩
  · exact closed
  · exact SourceCurrentSecondaryProjectionEndpoint.endpoint_closed unconstrained trace ready available

end MicroCFTA.SourceCurrentSecondaryProjectionAnchor
