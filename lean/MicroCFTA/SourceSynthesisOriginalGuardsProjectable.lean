import MicroCFTA.SourceSynthesisGeneralizeFiniteInstances
import MicroCFTA.SourceSynthesisNativeGuardOrigins
import MicroCFTA.SourceSynthesisFirstOrderTotality

/-!
# Projectable guards from original synthesis input

Finite witnesses satisfy the actual generated equality classes.
The completed normalizer therefore returns a present payload.
Every original alphabet guard and initial edge record has that property.
Generated native trace preservation remains separate.
-/
namespace MicroCFTA.SourceSynthesisOriginalGuardsProjectable
open Language InternedConstructorTemplates
open SourceSynthesisTypeSyntax (Ty Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisOriginalGuardAlphabet (applicationGuard filterGuard alphabet)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

/-- A finite raw-class witness excludes the contradictory normalized result. -/
private theorem eqGuard_projectable_of_satisfies {Label : Type}
    (classes : EqualityNormalize.Constraints) (term : Term Label)
    (satisfied : EqualityNormalize.Satisfies term classes) :
    ∃ output, SourceCompactGuards.sourceEqualities (eqGuard classes) = some output := by
  have normalized := (SourceEqualityPCSGuard.normalize_sat classes term).mpr satisfied
  cases computed : SourceCompactGuards.normalize classes with
  | none =>
      rw [computed] at normalized
      exact False.elim normalized
  | some output =>
      refine ⟨output, ?_⟩
      rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
      change SourceCompactGuards.normalize classes = some output
      exact computed

/-- Every actual generalized Type guard has a present source equality payload. -/
theorem generalized_projectable (typ : Ty) :
    ∃ classes, SourceCompactGuards.sourceEqualities (eqGuard (equalityClasses typ)) = some classes := by
  let substitution : String → Term Symbol :=
    fun _ => .node (SourceSynthesisLabelProgramBuildRoles.literal "") []
  exact eqGuard_projectable_of_satisfies (equalityClasses typ)
    (SourceSynthesisGeneralizeFiniteInstances.instantiate substitution typ)
    (SourceSynthesisGeneralizeFiniteInstances.generated_equalities substitution typ)

/-- The fixed application guard has a finite equality witness. -/
theorem application_projectable :
    ∃ classes, SourceCompactGuards.sourceEqualities applicationGuard = some classes := by
  let leaf : Term Unit := .node () []
  let term : Term Unit :=
    .node () [leaf, leaf, .node () [.node () [leaf, leaf, leaf]], .node () [leaf]]
  apply eqGuard_projectable_of_satisfies
    [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] term
  simp [EqualityNormalize.Satisfies, EqualityNormalize.ClassSat, PathsEqual, Term.atPath, term, leaf]

/-- The fixed filter guard has a finite equality witness. -/
theorem filter_projectable :
    ∃ classes, SourceCompactGuards.sourceEqualities filterGuard = some classes := by
  let leaf : Term Unit := .node () []
  let term : Term Unit := .node () [leaf, .node () [leaf]]
  apply eqGuard_projectable_of_satisfies [[[0], [1, 0]]] term
  simp [EqualityNormalize.Satisfies, EqualityNormalize.ClassSat, PathsEqual, Term.atPath, term, leaf]

/-- Every guard in the actual original alphabet has a present source payload. -/
theorem alphabet_projectable (lib : Library) (guard : Guard) (member : guard ∈ alphabet lib) :
    ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes := by
  simp only [alphabet, List.mem_cons, List.mem_append, List.mem_map] at member
  rcases member with rfl | rfl | rfl | ⟨entry, _included, rfl⟩ | ⟨entry, _included, rfl⟩
  · exact ⟨[], rfl⟩
  · exact application_projectable
  · exact filter_projectable
  · exact generalized_projectable entry.2.1
  · exact generalized_projectable entry.2

/-- The actual original build supplies projectability for all its physical edge records. -/
theorem initial_heap [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query size = .ok expression)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap) :
    SourceEqualityAnnotationHeap.Heap
      (fun guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes) heap := by
  have known := SourceSynthesisNativeGuardOrigins.initial_heap lib query size expression accepted value heap built
  intro key edge present
  exact alphabet_projectable lib key.constraint (known key edge present)

/-- Every nonnegative source request constructs its original expression and projectable heap. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (size : Int) (nonnegative : 0 ≤ size) :
    ∃ (expression : Expression) (value : Value Symbol Guard)
      (heap : InternedConstructorTemplates.State Symbol Guard),
      firstOrderRaw lib query size = .ok expression ∧
      InternedFreshOrdinaryConstruction.build
        (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap ∧
      SourceEqualityAnnotationHeap.Heap
        (fun guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes) heap := by
  obtain ⟨expression, accepted⟩ :=
    SourceSynthesisFirstOrderTotality.firstOrderRaw_total lib query size nonnegative
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete
    (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression)
  exact ⟨expression, value, heap, accepted, built,
    initial_heap lib query size expression accepted value heap built⟩

end MicroCFTA.SourceSynthesisOriginalGuardsProjectable
