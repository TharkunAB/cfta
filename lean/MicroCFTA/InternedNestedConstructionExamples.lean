import MicroCFTA.InternedNestedConstruction
import MicroCFTA.InternedNestedConstructionReplay
import MicroCFTA.InternedErasedEdgeReplay

/-!
# Complete closed nested constructor executions

The kernel evaluates the actual two-probe and reservation schedule. These
examples include a retained outer reference, an erased outer-dependent
edge, and repeated root self-union normalization.
-/
namespace MicroCFTA.InternedNestedConstructionExamples
open InternedConstructorTemplates InternedNestedConstruction
open InternedBinderProtocol (NodeRef Reference)

/-- An inner recursive node retains the fresh enclosing reference as a separate child. -/
def retained : Syntax Nat Unit := .binder true (.node
  [.mk 0 () [.var 0], .mk 1 () [.binder true (.node [.mk 2 () [.var 0, .var 1]])]])

/-- The inner node discards the outer-dependent edge because its other child is EmptyNode. -/
def erased : Syntax Nat Unit := .binder true (.node
  [.mk 0 () [.var 0], .mk 1 () [.binder true (.node [.mk 2 () [.var 0], .mk 3 () [.var 1, .empty]])]])

/-- Nested root unions exercise probe-name aliasing and the final bare-cycle cleanup. -/
def selfUnion : Syntax Nat Unit := .binder true (.binder true (.union [.var 0, .var 1]))

/-- All example variables are bound by their actual lexical source constructor. -/
theorem closed_examples : Scoped 0 retained ∧ Scoped 0 erased ∧ Scoped 0 selfUnion := by
  simp [retained, erased, selfUnion, Scoped, EdgesScoped, ManyScoped]

/-- Read only the returned record's observable fields and both final identity counters. -/
def summary : Outcome Symbol Guard (Value Symbol Guard) → Option (NodeRef × Nat × List Reference × Nat × Nat)
  | .pending _ _ => none
  | .done value state => some (value.referenceOf, value.depth, value.free, state.nodes.next, state.edges.next)

/-- The retained outer-dependent nested construction completes with no free reference. -/
theorem retained_completes : summary (build retained [] empty) = some (.mu 10, 2, [], 16, 15) := by cbv

/-- The erased outer-dependent nested construction reuses its earlier completed inner binder. -/
theorem erased_completes : summary (build erased [] empty) = some (.mu 6, 2, [], 8, 10) := by cbv

/-- Source self-union normalization and cleanup complete even when nested depth probes share a sentinel. -/
theorem selfUnion_completes : summary (build selfUnion [] empty) = some (.empty, 0, [], 11, 0) := by cbv

/-- The result summary can only report a value from a complete execution. -/
theorem summary_complete (outcome : Outcome Symbol Guard (Value Symbol Guard))
    (observed : summary outcome = some fields) : ∃ value state, outcome = .done value state := by
  cases outcome with
  | pending key state => cases observed
  | done value state => exact ⟨value, state, rfl⟩

/-- Every checked complete example retains its exact record and counters through arbitrary later cache growth. -/
theorem complete_summary_replays [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (observed : summary (build expression [] empty) = some fields) :
    ∃ value final, build expression [] empty = .done value final ∧
      ∀ after, Grows final after → build expression [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := summary_complete _ observed
  exact ⟨value, final, completed, fun after growth => empty_replay expression value final after completed growth⟩

end MicroCFTA.InternedNestedConstructionExamples
