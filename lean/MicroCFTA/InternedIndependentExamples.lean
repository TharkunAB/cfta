import MicroCFTA.InternedIndependentCompletion
import MicroCFTA.InternedNestedProvenance

/-!
# Independent nested source programs complete and retain their exact records

The examples use the same ancestor symbols and a union body. Completion
comes from lexical dependencies rather than a successful evaluation premise.
-/
namespace MicroCFTA.InternedIndependentCompletion
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedCoverage
open InternedNestedDependencies InternedNestedSpecialization

/-- Syntax-derived first completion supplies every actual record invariant and subsequent exact replay. -/
theorem closed_complete_record [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (staged : Staged expression) :
    ∃ value final, build expression [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build expression [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes expression staged
  have verified := closed_verified expression
  refine ⟨value, final, completed, ?_, closed_covered expression value final completed,
    verified.result value final completed, fun after growth => empty_replay expression value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

/-- Nested binders retain their own local variables while sharing the enclosing root symbol. -/
def sharedSymbols : Syntax Nat Unit := .binder false (.node
  [.mk 0 () [], .mk 0 () [.var 0,
    .binder true (.node [.mk 0 () [], .mk 0 () [.var 0,
      .binder false (.node [.mk 0 () [.var 0]])]])]])

/-- Actual source normalization removes each self member from a union body before key construction. -/
def selfUnions : Syntax Nat Unit := .binder true (.union
  [.var 0, .binder false (.union [.var 0, .node [.mk 0 () []]]),
    .node [.mk 0 () [.empty]], .empty])

/-- The independent dependency condition is computed from original lexical variables. -/
theorem examples_staged : Staged sharedSymbols ∧ Staged selfUnions := by
  simp [sharedSymbols, selfUnions, Staged, ManyStaged, EdgesStaged, Independent,
    ManyIndependent, EdgesIndependent, inputs, manyInputs, edgeInputs, enclosing]

/-- Each declared variable belongs to an actual enclosing source binder. -/
theorem examples_scoped : Scoped 0 sharedSymbols ∧ Scoped 0 selfUnions := by
  simp [sharedSymbols, selfUnions, Scoped, ManyScoped, EdgesScoped]

/-- Repeated ancestor symbols need no separation when nested callbacks are lexically independent. -/
theorem shared_symbols_complete :
    ∃ value final, build sharedSymbols [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build sharedSymbols [] after = .done value after :=
  closed_complete_record sharedSymbols examples_staged.1

/-- Self filtering, raw and smart binders, and empty-child removal retain complete canonical records. -/
theorem self_unions_complete :
    ∃ value final, build selfUnions [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build selfUnions [] after = .done value after :=
  closed_complete_record selfUnions examples_staged.2

end MicroCFTA.InternedIndependentCompletion
