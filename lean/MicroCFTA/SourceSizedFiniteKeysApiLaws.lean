import MicroCFTA.SourceSizedFiniteKeysPublic
import MicroCFTA.SourceSizedFiniteKeysDispatchApi
import MicroCFTA.SourceSizedApiLaws

/-!
# Complete Sized query laws for actual original-map dispatch

Validation derives the finite carrier from the original map keys. Every
successful public or raw-map reference and optimized result satisfies one
query specification at the original guarded language. The state type can
be infinite. Canonical row order and exact errors retain their source form.
-/
namespace MicroCFTA.SourceSizedFiniteKeysPublic
open Language RecursiveSize SourceSizedFiniteKeys SourceSizedDecided
open SourceGuards SourceObservations SourceSymbolicIndex SourceSizedPreprocessing SourceSizedDispatcher

variable {State Formula : Type} [DecidableEq State] [Ord State] [DecidableEq Formula]
    [Ord (Label Formula)] [Std.TransOrd (Label Formula)] [Std.LawfulEqOrd (Label Formula)]
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (active : ∀ state row, row ∈ lookup table state → SourceCompactGuards.ActiveOption row.constraint.equalities)
    (formulas : Formulas Formula) (solver : Entailment Formula)

include active

/-- Successful public dispatch derives the complete exact API at the original guarded language. -/
theorem public_exact (api : Api (Label Formula)) (success : publicSized (input table root valid) = .ok api) :
    SourceSizedApiLaws.Exact api (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  have membership := (public_correct table root valid active formulas solver api success).1
  have same := public_api_eq table root valid api success
  rw [same]
  apply SourceSizedApiLaws.reference
  intro term
  have source := membership (nodeSize term) term
  rw [same] at source
  have reference := SourceSizedReferenceAPI.signed_exact (equalityRows (nativeSorted table root valid)) root
    (nodeSize term : Int) term
  exact ⟨fun accepted => (source.mp (reference.mpr ⟨accepted, rfl⟩)).1,
    fun accepted => (reference.mp (source.mpr ⟨accepted, rfl⟩)).1⟩

/-- The public reference path satisfies the same finite exact query specification. -/
theorem reference_exact (api : Api (Label Formula)) (success : publicReference (input table root valid) = .ok api) :
    SourceSizedApiLaws.Exact api (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  apply public_exact table root valid active formulas solver api
  rwa [publicSized_eq_reference]

/-- The actual original-map reference has all exact laws without a finite original state type. -/
theorem native_reference_exact (api : Api (Label Formula))
    (success : SourceSizedFiniteKeysDispatch.nativeReference table root valid = .ok api) :
    SourceSizedApiLaws.Exact api (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  rw [SourceSizedFiniteKeysDispatch.nativeReference_eq] at success
  exact reference_exact table root valid active formulas solver api success

/-- Actual original-map optimized dispatch uses the identical complete reference sequence. -/
theorem native_sized_exact (api : Api (Label Formula))
    (success : SourceSizedFiniteKeysDispatch.nativeSized table root valid = .ok api) :
    SourceSizedApiLaws.Exact api (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  rw [SourceSizedFiniteKeysDispatch.nativeSized_eq] at success
  exact public_exact table root valid active formulas solver api success

end MicroCFTA.SourceSizedFiniteKeysPublic
