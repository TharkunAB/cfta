import MicroCFTA.InternedSourceClassSelection

/-!
# Finite complete selection and per-occurrence source readback

Every ready cache supplies finite class decisions. Returned cache growth
retains the original child list for all later class queries. The resulting
receipts determine the exact selected order and complete final cache.
-/
namespace MicroCFTA.InternedSourceClassSelection
open Cache InternedConstructorTemplates InternedNestedConstruction EqualityNormalize
open InternedRecordCoherence InternedProbeProvenance
open InternedFreshOrdinaryGateRank (Node)

/-- Every recorded class occurrence has its exact complete source graph. -/
theorem Trace.query_valid [DecidableEq (EdgeKey Symbol Guard)] {unconstrained : Value Symbol Guard → Bool}
    (trace : Trace unconstrained values classes state queries final)
    (query : Query Symbol Guard) (member : query ∈ queries) :
    InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values query.paths query.before query.blocked query.after := by
  induction trace with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact ih member

/-- Complete selection graphs determine all class receipts and the complete final constructor cache. -/
theorem Trace.unique [DecidableEq (EdgeKey Symbol Guard)] {unconstrained : Value Symbol Guard → Bool}
    (left : Trace unconstrained values classes state first firstState)
    (right : Trace unconstrained values classes state second secondState) : first = second ∧ firstState = secondState := by
  induction left generalizing second secondState with
  | nil => cases right; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      cases right with
      | cons otherHead otherTail =>
          obtain ⟨rfl, rfl⟩ := InternedFreshOrdinaryStatefulGateTrace.class_trace_unique _ _ _ _ _ _ _ _ head otherHead
          obtain ⟨rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl⟩

/-- Every complete false class query gives a complete false query for each original path. -/
theorem clear_paths [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state final : State Symbol Guard)
    (trace : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths state false final) :
    ∀ path ∈ paths, ∃ before after, InternedFreshOrdinaryStatefulGateTrace.PathTrace unconstrained values path before false after := by
  induction paths generalizing state with
  | nil => simp
  | cons first rest ih =>
      cases trace with
      | next head tail =>
          intro path member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_, _, head⟩
          · exact ih _ tail path member

/-- Every selected class contains only completed false source path queries. -/
theorem Trace.selected_paths [DecidableEq (EdgeKey Symbol Guard)] {unconstrained : Value Symbol Guard → Bool}
    (trace : Trace unconstrained values classes state queries final)
    (paths : Class) (member : paths ∈ selected queries) :
    ∀ path ∈ paths, ∃ before after, InternedFreshOrdinaryStatefulGateTrace.PathTrace unconstrained values path before false after := by
  obtain ⟨before, after, clear⟩ := trace.selected_witness paths member
  exact clear_paths unconstrained values paths before after clear

/-- Every ready original child list has complete selection with all intermediate constructor invariants. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (classes : Constraints) :
    ∃ queries, ∃ after : Node Symbol Guard,
      Trace unconstrained values classes node.state queries after.state ∧
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued := by
  revert available
  induction classes generalizing node with
  | nil => intro available; exact ⟨[], node, .nil, grows_refl _, extends_refl _⟩
  | cons paths rest ih =>
      intro available
      obtain ⟨bound, blocked, after, head, growth, history, _⟩ :=
        InternedFreshOrdinaryStatefulGateTrace.cached_class_trace unconstrained node values available paths
      obtain ⟨queries, final, tail, tailGrowth, tailHistory⟩ := ih after
        (fun value member => (available value member).grows _ _ growth history)
      exact ⟨_, final, .cons head tail, grows_trans growth tailGrowth, extends_trans history tailHistory⟩

/-- One finite fuel amount completes all local classes and every larger amount has the same exact readback. -/
theorem eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (classes : Constraints) :
    ∃ bound queries, ∃ after : Node Symbol Guard,
      Trace unconstrained values classes node.state queries after.state ∧
      Grows node.state after.state ∧ Extends node.state.nodes.issued after.state.nodes.issued ∧
      ∀ extra, select unconstrained (bound + extra) values classes node.state = .done (some (selected queries)) after.state := by
  obtain ⟨queries, after, trace, growth, history⟩ := complete unconstrained node values available classes
  obtain ⟨bound, done⟩ := trace_complete _ _ _ _ _ _ trace
  exact ⟨bound, queries, after, trace, growth, history, fun extra => fuel_stable _ bound extra _ _ _ _ _ done⟩

end MicroCFTA.InternedSourceClassSelection
