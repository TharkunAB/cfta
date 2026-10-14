import MicroCFTA.InternedSourceClassSelectionComplete
import MicroCFTA.InternedSourceGateReplay

/-!
# Pure class-selection readback in the retained final cache

Every original class receipt replays in the complete final selection cache.
The finite source gate defines a total pure decision in a ready cache.
These derived decisions give exactly EqualityReduction.selectedClasses.
-/
namespace MicroCFTA.InternedSourceClassSelection
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshOrdinaryGateRank (Node)
open InternedFreshOrdinaryMemoGateTrace (Ready)
open EqualityNormalize

/-- Every class receipt replays exactly above the complete selection's final cache. -/
theorem Trace.replay [DecidableEq (EdgeKey Symbol Guard)] {unconstrained : Value Symbol Guard → Bool}
    (trace : Trace unconstrained values classes state queries final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value) :
    Ready final ∧ Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      ∀ target, Grows final target → ∀ query ∈ queries,
        InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values query.paths target query.blocked target := by
  revert available ready
  induction trace with
  | nil => intro ready available; exact ⟨ready, grows_refl _, extends_refl _, by intros; contradiction⟩
  | cons head tail ih =>
      intro ready available
      obtain ⟨middleReady, firstGrowth, firstHistory, firstReplay⟩ :=
        InternedSourceGateReplay.class_replay _ _ _ _ _ _ head ready available
      obtain ⟨finalReady, growth, history, replay⟩ := ih middleReady
        (fun value member => (available value member).grows _ _ firstGrowth firstHistory)
      refine ⟨finalReady, grows_trans firstGrowth growth, extends_trans firstHistory history, ?_⟩
      intro target retained query member
      rcases List.mem_cons.mp member with rfl | member
      · exact firstReplay target (grows_trans growth retained)
      · exact replay target retained query member

/-- Finite class execution supplies a Boolean and its complete logical source graph. -/
theorem decision_exists [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
    ∃ answer, ∃ after : State Symbol Guard,
      InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths node.state answer after := by
  obtain ⟨bound, answer, after, trace, _⟩ :=
    InternedFreshOrdinaryStatefulGateTrace.cached_class_trace unconstrained node values available paths
  exact ⟨answer, after.state, trace⟩

/-- The completed source gate defines a pure class decision in each certified cache. -/
noncomputable def decision [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) : Bool :=
  Classical.choose (decision_exists unconstrained node values available paths)

/-- The chosen pure decision has an actual complete source class graph. -/
theorem decision_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
    ∃ after : State Symbol Guard,
      InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths node.state
        (decision unconstrained node values available paths) after :=
  Classical.choose_spec (decision_exists unconstrained node values available paths)

/-- Install the derived total source class decision in the existing equality-reduction operations. -/
noncomputable def guarded [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (ops : EqualityReduction.Operations (Value Symbol Guard) TermSymbol) :
    EqualityReduction.Operations (Value Symbol Guard) TermSymbol := by
  classical
  exact { ops with blocked := fun values paths =>
    if available : ∀ value ∈ values, Available node.state value then decision unconstrained node values available paths else true }

/-- Exact per-occurrence decisions determine the same ordered pure list filter. -/
theorem selected_eq_filter (queries : List (Query Symbol Guard)) (blocked : Class → Bool)
    (checked : ∀ query ∈ queries, query.blocked = blocked query.paths) :
    selected queries = (queries.map Query.paths).filter (fun paths => !blocked paths) := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      rw [selected_cons, List.map_cons, List.filter_cons, ← checked query List.mem_cons_self]
      have tail := ih (fun other member => checked other (List.mem_cons_of_mem query member))
      rw [← tail]
      cases query.blocked <;> rfl

/-- Actual ordered selection equals the pure selectedClasses operation in its retained final cache. -/
theorem Trace.selected_eq_guarded [DecidableEq (EdgeKey Symbol Guard)] {unconstrained : Value Symbol Guard → Bool}
    (node : Node Symbol Guard) (trace : Trace unconstrained values classes state queries node.state)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (ops : EqualityReduction.Operations (Value Symbol Guard) TermSymbol) :
    selected queries = EqualityReduction.selectedClasses (guarded unconstrained node ops) classes values := by
  classical
  obtain ⟨_, growth, history, replay⟩ := trace.replay ready available
  have finalAvailable : ∀ value ∈ values, Available node.state value :=
    fun value member => (available value member).grows _ _ growth history
  have checked : ∀ query ∈ queries, query.blocked = (guarded unconstrained node ops).blocked values query.paths := by
    intro query member
    obtain ⟨after, actual⟩ := decision_complete unconstrained node values finalAvailable query.paths
    have exact := InternedFreshOrdinaryStatefulGateTrace.class_trace_unique _ _ _ _ _ _ _ _
      (replay node.state (grows_refl _) query member) actual
    simpa only [guarded, dite_eq_left finalAvailable] using exact.1
  simpa only [trace.original, EqualityReduction.selectedClasses] using selected_eq_filter queries
    ((guarded unconstrained node ops).blocked values) checked

/-- Replacing the class gate with the derived source gate retains every existing local semantic law. -/
theorem guarded_laws [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (ops : EqualityReduction.Operations (Value Symbol Guard) TermSymbol)
    (laws : EqualityReduction.Laws ops) : EqualityReduction.Laws (guarded unconstrained node ops) where
  empty := laws.empty
  intersect := laws.intersect
  project := laws.project
  require_narrow := laws.require_narrow
  require_keep := laws.require_keep
  edit_narrow := laws.edit_narrow
  edit_keep := laws.edit_keep
  contradiction := laws.contradiction

/-- Finish the existing one-pass reduction with the classes returned by actual ordered gate selection. -/
def finish [DecidableEq (Value Symbol Guard)] (ops : EqualityReduction.Operations (Value Symbol Guard) TermSymbol)
    (classes inherited kept : Constraints) (values : List (Value Symbol Guard)) : List (Value Symbol Guard) :=
  if classes = [] ∧ inherited = [] then values
  else if ops.contradictory classes inherited then values.map (fun _ => ops.empty)
  else EqualityReduction.propagate ops
    (kept.foldr (EqualityReduction.reduceClass ops) (ops.requireAll kept.flatten values))

/-- The source selection receipts supply exactly the classes used by the existing pure reduction pass. -/
theorem Trace.pass_readback [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} (node : Node Symbol Guard)
    (trace : Trace unconstrained values classes state queries node.state)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (ops : EqualityReduction.Operations (Value Symbol Guard) TermSymbol) (inherited : Constraints) :
    finish ops classes inherited (selected queries) values =
      EqualityReduction.pass (guarded unconstrained node ops) classes inherited values := by
  unfold finish EqualityReduction.pass
  rw [← trace.selected_eq_guarded node ready available ops]
  rfl

/-- Derived complete gate selection preserves the existing exact one-pass forest theorem. -/
theorem Trace.pass_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} (node : Node Symbol Guard)
    (trace : Trace unconstrained values classes state queries node.state)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (ops : EqualityReduction.Operations (Value Symbol Guard) TermSymbol) (laws : EqualityReduction.Laws ops)
    (inherited : Constraints) (active : Active classes)
    (nonroot : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (term : Language.Term TermSymbol)
    (satisfied : Satisfies term classes ∧ Satisfies term inherited) :
    EqualityReduction.Forest ops (finish ops classes inherited (selected queries) values) term ↔ EqualityReduction.Forest ops values term := by
  rw [trace.pass_readback node ready available ops inherited]
  exact EqualityReduction.pass_exact (guarded unconstrained node ops) (guarded_laws unconstrained node ops laws)
    classes inherited active nonroot values term satisfied

end MicroCFTA.InternedSourceClassSelection
