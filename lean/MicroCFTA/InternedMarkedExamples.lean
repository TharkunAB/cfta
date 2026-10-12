import MicroCFTA.InternedMarkedCompletion
import MicroCFTA.InternedNestedConstructionReplay

/-!
# Closed marked nested constructors complete and replay

Sibling binders can reuse a marker. Only an active enclosing binder's
marker is excluded. Child unions and empty branches remain permitted.
-/
namespace MicroCFTA.InternedMarkedConstruction
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedCoverage
open InternedNestedRootLabels

/-- A marked input derives complete canonical records and exact replay without a first-run success premise. -/
theorem closed_complete_record [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (tagged : Tagged [] expression) :
    ∃ value final, build expression [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build expression [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes expression tagged
  have verified := closed_verified expression
  refine ⟨value, final, completed, ?_, closed_covered expression value final completed,
    verified.result value final completed, fun after growth => empty_replay expression value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

/-- The nested body retains its enclosing variable and permits arbitrary union and empty children. -/
def markedNested : Syntax Nat Unit := .binder true (.node
  [.mk 10 () [], .mk 10 () [.var 0,
    .binder true (.node [.mk 11 () [], .mk 11 () [.var 0, .var 1, .union [.empty, .node [.mk 42 () []]]]])]])

/-- Separate sibling requests can reuse a root marker after their earlier request has completed. -/
def markedSiblings : Syntax Nat Unit := .binder true (.node
  [.mk 10 () [], .mk 10 () [.var 0,
    .binder true (.node [.mk 11 () [], .mk 11 () [.var 0, .var 1]]),
    .binder false (.node [.mk 11 () [], .mk 11 () [.var 0, .empty]])]])

/-- The completion condition is checked on declarations before any probes or node identities exist. -/
theorem examples_tagged : Tagged [] markedNested ∧ Tagged [] markedSiblings := by
  simp [markedNested, markedSiblings, Tagged, EdgesTagged, ManyTagged, Marked, declared]
  exact ⟨10, by decide⟩

/-- Both examples close every lexical variable under its actual source binder. -/
theorem examples_scoped : Scoped 0 markedNested ∧ Scoped 0 markedSiblings := by
  simp [markedNested, markedSiblings, Scoped, EdgesScoped, ManyScoped]

/-- Fresh-dependent nested children and erased branches complete with canonical available records. -/
theorem nested_complete :
    ∃ value final, build markedNested [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build markedNested [] after = .done value after :=
  closed_complete_record markedNested examples_tagged.1

/-- Completed sibling sharing requires no global uniqueness of binder marker symbols. -/
theorem siblings_complete :
    ∃ value final, build markedSiblings [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build markedSiblings [] after = .done value after :=
  closed_complete_record markedSiblings examples_tagged.2

end MicroCFTA.InternedMarkedConstruction
