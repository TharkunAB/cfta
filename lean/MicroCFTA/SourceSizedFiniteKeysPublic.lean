import MicroCFTA.SourceSizedFiniteKeysCanonical

/-!
# Public Sized contracts for finite explicit row maps

Validation supplies the finite state carrier from actual table keys.
The raw constraint invariant survives restriction and structural trim.
The resulting public API refers to the original table language, even when
the original state type is infinite. No input-correspondence premise is used.
-/
namespace MicroCFTA.SourceSizedFiniteKeysPublic
open Language RecursiveSize SourceSizedFiniteKeys SourceSizedDecided
open SourceGuards SourceObservations SourceSymbolicIndex SourceSizedPreprocessing SourceSizedDispatcher

variable {State : Type} [DecidableEq State] [Ord State]

/-- Every finite restricted row comes from the original lookup with its constraint unchanged. -/
theorem restricted_active
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula))
    (closed : SourceSizedFiniteKeys.Closed table)
    (active : ∀ state row, row ∈ lookup table state → SourceCompactGuards.ActiveOption row.constraint.equalities)
    (state : SourceDenseRows.Member (SourceDenseRows.keys table)) (row)
    (member : row ∈ restricted table closed state) : SourceCompactGuards.ActiveOption row.constraint.equalities := by
  have source : forget row ∈ lookup table state.val := by
    rw [← rows_readback table closed state]
    exact List.mem_map.mpr ⟨row, member, rfl⟩
  exact active state.val (forget row) source

/-- Structural trim retains the active-constraint invariant derived from the raw table. -/
theorem trimmed_active [DecidableEq Formula]
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (active : ∀ state row, row ∈ lookup table state → SourceCompactGuards.ActiveOption row.constraint.equalities)
    (state row)
    (member : row ∈ SourceSizedTrimGuards.trimmedRows (input table root valid).rows
      (input table root valid).states (input table root valid).root state) :
    SourceCompactGuards.ActiveOption row.constraint.equalities := by
  unfold SourceSizedTrimGuards.trimmedRows at member
  split at member
  · exact restricted_active table _ active state row (List.mem_filter.mp member).1
  · simp at member

/-- Restricting the validated table preserves each exact ordered reference class and its finite evaluation. -/
theorem reference_correct [DecidableEq Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (holds : Payload → Term Symbol → Bool) (size : Nat) :
    SourceSizedReference.classes (automaton (input table root valid).rows holds) size (input table root valid).root =
      SourceSizedReference.classes (automaton (lookup table) holds) size root ∧
    SourceSizedReference.ClassEvaluation (automaton (input table root valid).rows holds) (size + 1) size
      (input table root valid).root (SourceSizedReference.classes (automaton (lookup table) holds) size root) := by
  have same := classes_exact table (validated_closed table root valid) holds (input table root valid).root size
  change SourceSizedReference.classes (automaton (input table root valid).rows holds) size (input table root valid).root =
    SourceSizedReference.classes (automaton (lookup table) holds) size root at same
  refine ⟨same, ?_⟩
  rw [← same]
  exact SourceSizedReference.classes_evaluation_bound _ size _

/-- Successful public dispatch has the exact original guarded language and complete distinct size order. -/
theorem public_correct [DecidableEq Formula] [Ord (Label Formula)]
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (active : ∀ state row, row ∈ lookup table state → SourceCompactGuards.ActiveOption row.constraint.equalities)
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (api : Api (Label Formula)) (success : publicSized (input table root valid) = .ok api) :
    (∀ (size : Nat) term, term ∈ api.terms (size : Int) ↔
      Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root term ∧ nodeSize term = size) ∧
    (∀ size, SourceSizedReference.ClassEvaluation (equalityRows (sortedRows (input table root valid)))
      (size + 1) size (input table root valid).root (api.terms (size : Int))) ∧
    (∀ bound, (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Nodup ∧
      (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Pairwise
        (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ term, (∃ bound, term ∈ SourceSizedQueries.through (fun size : Nat => api.terms size) bound) ↔
      Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root term) ∧
    (∀ size rank term, (api.rank term).map (fun position => (Int.ofNat position.size, Int.ofNat position.rank)) =
      some (size, rank) ↔ api.unrank size rank = some term) := by
  obtain ⟨membership, finite, ordered, unique, coverage, inverses⟩ :=
    SizedLanguageTheorem.public_correct formulas solver (input table root valid)
      (trimmed_active table root valid active) api success
  refine ⟨?_, finite, fun bound => ⟨unique bound, ordered bound⟩, ?_, inverses⟩
  · intro size term
    rw [membership, input_language]
  · intro term
    rw [coverage, input_language]


/-- All four public query functions read the actual original-state canonical reference sequence. -/
theorem public_api_eq [DecidableEq Formula] [Ord (Label Formula)]
    [Std.TransOrd (Label Formula)] [Std.LawfulEqOrd (Label Formula)]
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (api : Api (Label Formula)) (success : publicSized (input table root valid) = .ok api) :
    api = referenceApi (equalityRows (nativeSorted table root valid)) root := by
  obtain ⟨_, same⟩ := publicSized_success (input table root valid) api success
  rw [same]
  have classes : (fun size => SourceSizedReference.classes (equalityRows (sortedRows (input table root valid))) size
      (input table root valid).root) =
      (fun size => SourceSizedReference.classes (equalityRows (nativeSorted table root valid)) size root) := by
    funext size
    exact sorted_classes_exact table root valid SourceSizedEqualities.constraintHolds (input table root valid).root size
  unfold referenceApi
  rw [classes]

end MicroCFTA.SourceSizedFiniteKeysPublic
