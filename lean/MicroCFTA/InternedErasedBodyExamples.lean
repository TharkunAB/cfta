import MicroCFTA.InternedErasedBodyCompletion
import MicroCFTA.InternedIndependentCompletion

/-!
# Closed examples read and then erase their enclosing dependency

The inner binder reads lexical slot one in a dead edge. It also retains its
own local recursion in a live edge. First completion follows from the
actual enclosing probe schedule, with identical ancestor symbols permitted.
-/
namespace MicroCFTA.InternedErasedBodyExamples
open InternedConstructorTemplates InternedNestedConstruction InternedNestedOrdinary
open InternedStagedBinders (EdgeSkeleton)
open InternedNestedErasedEdge InternedErasedBodyResidual
open InternedNestedDependencies InternedNestedSpecialization
open InternedNestedFacts InternedRecordCoherence InternedProbeProvenance

/-- Live inner recursion uses the same symbol as every enclosing edge. -/
def live : List (EdgeSkeleton Nat Unit) := [.mk 0 () [], .mk 0 () [.argument]]

/-- The original callback reads its enclosing value before empty-child removal. -/
def inner (smart : Bool) : Syntax Nat Unit := .binder smart (source (body live 0 ()))

/-- Ordinary nodes and unions can contain both raw and smart erased-dependent calls. -/
def outerBody : Syntax Nat Unit := .node
  [.mk 0 () [], .mk 0 () [.var 0, inner false, .union [.empty, inner true]]]

/-- The declared source shape, rather than a successful request, establishes admission. -/
theorem admitted : Admitted outerBody := by
  simp only [outerBody, Admitted, EdgesAdmitted, ManyAdmitted, inner, and_true, true_and]
  exact ⟨⟨live, 0, (), rfl⟩, ⟨live, 0, (), rfl⟩⟩

/-- Every lexical variable has its actual enclosing source binder. -/
theorem closed_scope : Scoped 0 (.binder true outerBody) := by
  simp [outerBody, inner, live, body, source, sourceEdges, sourceMany, shiftEdges, shiftMany, shift,
    Scoped, ManyScoped, EdgesScoped]

/-- The inner source expression has a real enclosing dependency before normalization. -/
theorem reads_outer (smart : Bool) : 0 ∈ inputs (inner smart) := by
  simp [inner, live, body, source, sourceEdges, sourceMany, shiftEdges, shiftMany, shift,
    inputs, manyInputs, edgeInputs, enclosing]

/-- Lexical independence alone cannot justify this enclosing callback. -/
theorem outside_independent_fragment : ¬ InternedIndependentCompletion.Staged (.binder true outerBody) := by
  simp [InternedIndependentCompletion.Staged, outerBody, Independent, EdgesIndependent,
    ManyIndependent, inner, live, body, source, sourceEdges, sourceMany, shiftEdges, shiftMany, shift,
    inputs, manyInputs, edgeInputs, enclosing]

/-- Actual source completion derives all cache provenance and subsequent exact whole-program replay. -/
theorem complete :
    ∃ value final, build (.binder true outerBody) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (.binder true outerBody) [] after = .done value after :=
  closed_complete_record true outerBody admitted

end MicroCFTA.InternedErasedBodyExamples
