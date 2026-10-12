import MicroCFTA.InternedCombinedCompletion
import MicroCFTA.InternedNestedInputScope
import MicroCFTA.InternedIndependentExamples
import MicroCFTA.InternedErasedBodyExamples

/-!
# Retained, independent, and erased dependencies share one source execution

The outer retained binders create two pending ancestor frames. Their child
positions contain closed independent and erased-dependent subprograms.
The first source depth trace prepares those calls for later fresh callbacks.
-/
namespace MicroCFTA.InternedCombinedConstruction
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedNestedCoverage InternedNestedDependencies
open InternedNestedPreparedSites

/-- The combined source condition supplies first completion, every record invariant, and exact subsequent replay. -/
theorem closed_complete_record [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (combined : Combined 0 expression) :
    ∃ value final, build expression [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build expression [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes expression combined
  have verified := closed_verified expression
  refine ⟨value, final, completed, ?_, closed_covered expression value final completed,
    verified.result value final completed, fun after growth => empty_replay expression value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

/-- The inner retained binder contains both a closed independent program and a closed erased-body program. -/
def mixedEdges : List (EdgeSyntax Nat Unit) :=
  [.mk 0 () [.var 1], .mk 0 () [.var 0,
    InternedIndependentCompletion.sharedSymbols,
    .binder true InternedErasedBodyExamples.outerBody]]

/-- The closed source program evaluates all three completion mechanisms in one nested construction. -/
def mixed : Syntax Nat Unit := .binder true (.node [.mk 0 () [.var 0, .binder false (.node mixedEdges)]])

/-- Closed lexical scope supplies the independent subprogram's empty original input inventory. -/
theorem independent_leaf : Leaf InternedIndependentCompletion.sharedSymbols :=
  ⟨closed_inputs _ InternedIndependentCompletion.examples_scoped.1,
    Or.inl InternedIndependentCompletion.examples_staged.1⟩

/-- The erased subprogram closes its own enclosing dependency internally before it returns to retained ancestors. -/
theorem erased_leaf : Leaf (.binder true InternedErasedBodyExamples.outerBody) :=
  ⟨closed_inputs _ InternedErasedBodyExamples.closed_scope,
    Or.inr ⟨true, _, rfl, InternedErasedBodyExamples.admitted⟩⟩

/-- The mixed completion certificate comes entirely from source declarations and previously derived closed fragments. -/
theorem mixed_combined : Combined 0 mixed := by
  have variableCert (depth index : Nat) : Combined depth (.var index : Syntax Nat Unit) := by
    rw [Combined.eq_def]
    exact Or.inr trivial
  have independent (depth : Nat) : Combined depth InternedIndependentCompletion.sharedSymbols := by
    rw [Combined.eq_def]
    exact Or.inl independent_leaf
  have erased (depth : Nat) : Combined depth (.binder true InternedErasedBodyExamples.outerBody) := by
    rw [Combined.eq_def]
    exact Or.inl erased_leaf
  have rows : EdgesCombined 2 mixedEdges := by
    simp only [mixedEdges, EdgesCombined, ManyCombined, variableCert, independent, erased, and_self]
  have inner : Combined 1 (.binder false (.node mixedEdges)) := by
    rw [Combined.eq_def]
    refine Or.inr ⟨?_, rows⟩
    intro index bound
    have same : index = 0 := by omega
    subst index
    exact ⟨0, (), by simp [mixedEdges]⟩
  rw [mixed, Combined.eq_def]
  refine Or.inr ⟨?_, ?_⟩
  · intro index impossible
    omega
  · simpa only [EdgesCombined, ManyCombined, variableCert, true_and, and_true] using inner

/-- Every original source variable belongs to one of the actual lexical binders. -/
theorem mixed_scoped : Scoped 0 mixed := by
  simp [mixed, mixedEdges, InternedIndependentCompletion.sharedSymbols,
    InternedErasedBodyExamples.outerBody, InternedErasedBodyExamples.inner, InternedErasedBodyExamples.live,
    InternedNestedErasedEdge.body, InternedNestedErasedEdge.shiftEdges, InternedNestedErasedEdge.shiftMany,
    InternedNestedErasedEdge.shift, InternedNestedOrdinary.source, InternedNestedOrdinary.sourceEdges,
    InternedNestedOrdinary.sourceMany, Scoped, ManyScoped, EdgesScoped]

/-- Actual mixed first execution completes without assumed trace readiness or a successful initial run. -/
theorem mixed_complete :
    ∃ value final, build mixed [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build mixed [] after = .done value after :=
  closed_complete_record mixed mixed_combined

end MicroCFTA.InternedCombinedConstruction
