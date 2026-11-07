import MicroCFTA.SourceSizedConjunctionCurrent
import MicroCFTA.SourceSizedStructuralKeys
import MicroCFTA.SourceSizedReferenceAPI

/-!
# Current raw constraints in the reference value route

`Sized.hs:213-232` scans structurally trimmed rows for residual guards.
Its reference classes read the original sorted rows and call equalitiesHold.
The current equality accessor includes the positive guard before that test.
Agreement on retained rows therefore gives the original root language.

The final endpoint derives its finite carrier from current structural FTA
validation. It permits arbitrary raw equality fields. It needs no grouping,
ActiveOption, or SyntaxValid premise. Deep positive equalities and ambiguous
rows can use this route. Residual guards on retained rows cause an error.

These laws concern returned reference values. They do not prove selection
of this route by the mixed dispatcher, native container correspondence,
or completion of external IO evaluations. Sizes are unbounded integers.
-/

namespace MicroCFTA.SourceSizedReferenceCurrent

open Language RecursiveSize SourceSizedDecided SourceSizedDispatcher SourceSizedPreprocessing
open SourceGuards SourceObservations SourceSymbolicIndex SourceCompactGuards

variable {State Formula : Type}

/-- A positive guard makes the actual equality worker equal the current raw entry. -/
theorem constraintHolds_current [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula)
    (positiveGuard : (positive constraint.guard).isSome = true)
    (term : Term (Label Formula)) :
    SourceSizedEqualities.constraintHolds constraint term =
      SourceConstraintEntryRaw.acceptsConstraint formulas solver constraint term := by
  unfold SourceSizedEqualities.constraintHolds
  split
  next bottom => simp [bottom, positive] at positiveGuard
  next =>
    rw [SourceSizedEqualities.equalitiesHold_eq]
    exact (SourceSizedConjunctionCurrent.positive_entry formulas solver constraint positiveGuard term).symm

/-- The actual trimmed residual scan suffices for arbitrary raw constraint fields. -/
theorem residual_language [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (passed : residualCheck rows states root = true) (term : Term (Label Formula)) :
    Accepts (equalityRows rows) root term ↔
      Accepts (automaton rows (SourceConstraintEntryRaw.acceptsConstraint formulas solver)) root term := by
  apply SourceSizedTrimGuards.guards_exact rows states complete root
  intro state row member candidate
  have positiveGuard := List.all_eq_true.mp
    (List.all_eq_true.mp passed state (complete state)) row member
  exact constraintHolds_current formulas solver row.constraint positiveGuard candidate

/-- The source signed class is exact for the original current guarded language. -/
theorem signed_classes_exact [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (passed : residualCheck rows states root = true) (size : Int) (term : Term (Label Formula)) :
    term ∈ SourceSizedQueries.termsSigned
      (fun size => SourceSizedReference.classes (equalityRows rows) size root) size ↔
      Accepts (automaton rows (SourceConstraintEntryRaw.acceptsConstraint formulas solver)) root term ∧
        (nodeSize term : Int) = size := by
  rw [SourceSizedReferenceAPI.signed_exact]
  exact and_congr_left (fun _ => residual_language formulas solver rows states complete root passed term)

private theorem reference_success [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api) :
    residualCheck input.rows input.states input.root = true ∧
      api = referenceApi (equalityRows (sortedRows input)) input.root := by
  unfold publicReference at success
  split at success
  next passed => exact ⟨passed, (Except.ok.inj success).symm⟩
  next => cases success

/-- Canonical sorting preserves exact current acceptance at every signed size. -/
theorem public_signed_exact [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api)
    (size : Int) (term : Term (Label Formula)) :
    term ∈ api.terms size ↔
      Accepts (automaton input.rows (SourceConstraintEntryRaw.acceptsConstraint formulas solver)) input.root term ∧
        (nodeSize term : Int) = size := by
  obtain ⟨passed, same⟩ := reference_success input api success
  have sortedPassed : residualCheck (sortedRows input) input.states input.root = true := by
    rw [← residualCheck_perm input.rows (sortedRows input)
      (fun state => (sortedRows_perm input state).symm)]
    exact passed
  rw [same]
  change term ∈ SourceSizedQueries.termsSigned
    (fun size => SourceSizedReference.classes (equalityRows (sortedRows input)) size input.root) size ↔ _
  rw [signed_classes_exact formulas solver (sortedRows input) input.states input.complete input.root sortedPassed]
  exact and_congr_left (fun _ => SourceCyclicAutomaton.permutation_language
    (automaton input.rows (SourceConstraintEntryRaw.acceptsConstraint formulas solver))
    (automaton (sortedRows input) (SourceConstraintEntryRaw.acceptsConstraint formulas solver))
    (fun state => (sortedRows_perm input state).map _) input.root term)

/-- Natural-size classes have the same exact membership without a cache invariant. -/
theorem public_nat_exact [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api)
    (size : Nat) (term : Term (Label Formula)) :
    term ∈ api.terms (size : Int) ↔
      Accepts (automaton input.rows (SourceConstraintEntryRaw.acceptsConstraint formulas solver)) input.root term ∧
        nodeSize term = size := by
  have exact := public_signed_exact formulas solver input api success (size : Int) term
  constructor
  · intro member
    obtain ⟨accepted, sized⟩ := exact.mp member
    exact ⟨accepted, by omega⟩
  · rintro ⟨accepted, sized⟩
    exact exact.mpr ⟨accepted, by omega⟩

private theorem public_classes [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api) :
    (fun size : Nat => api.terms (size : Int)) =
      (fun size => SourceSizedReference.classes (equalityRows (sortedRows input)) size input.root) := by
  obtain ⟨_, same⟩ := reference_success input api success
  funext size
  rw [same]
  exact SourceSizedQueries.termsSigned_nat
    (fun size => SourceSizedReference.classes (equalityRows (sortedRows input)) size input.root)
    (SourceSizedReference.classes_zero (equalityRows (sortedRows input)) input.root) size

/-- Every returned reference class has a finite evaluation at its computed size bound. -/
theorem public_finite [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api) (size : Nat) :
    SourceSizedReference.ClassEvaluation (equalityRows (sortedRows input)) (size + 1) size
      input.root (api.terms (size : Int)) := by
  have same := congrFun (public_classes input api success) size
  rw [same]
  exact SourceSizedReference.classes_evaluation_bound _ size input.root

/-- Reference prefixes are ordered and contain each term only once. -/
theorem public_prefix_distinct_ordered [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api) (bound : Nat) :
    (SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound).Nodup ∧
      (SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound).Pairwise
        (fun first second => nodeSize first ≤ nodeSize second) := by
  rw [public_classes input api success]
  exact ⟨SourceSizedReferenceAPI.through_nodup _ input.root bound,
    SourceSizedReferenceAPI.through_ordered _ input.root bound⟩

/-- Every original accepted finite term occurs after finitely many reference classes. -/
theorem public_complete [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api) (term : Term (Label Formula)) :
    (∃ bound, term ∈ SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound) ↔
      Accepts (automaton input.rows (SourceConstraintEntryRaw.acceptsConstraint formulas solver)) input.root term :=
  SourceSizedQueries.prefix_complete _ nodeSize _
    (fun size term => public_nat_exact formulas solver input api success size term) term

/-- Both signed inverse laws hold for the actual returned reference query record. -/
theorem public_signed_inverses [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicReference input = .ok api)
    (size rank : Int) (term : Term (Label Formula)) :
    (api.rank term).map (fun position => ((position.size : Int), (position.rank : Int))) = some (size, rank) ↔
      api.unrank size rank = some term := by
  obtain ⟨_, rfl⟩ := reference_success input api success
  let classes := fun size => SourceSizedReference.classes (equalityRows (sortedRows input)) size input.root
  have sized : SourceSizedQueries.Sized classes nodeSize :=
    SourceSizedReferenceAPI.classes_sized _ input.root
  have unique : ∀ size, (classes size).Nodup := fun size => SourceSizedReference.classes_nodup _ size input.root
  change SourceSizedQueries.rankSigned classes nodeSize term = some (size, rank) ↔
    SourceSizedQueries.unrankSigned classes size rank = some term
  constructor
  · exact SourceSizedQueries.unrankSigned_rankSigned classes (SourceSizedReference.classes_zero _ input.root)
      nodeSize term size rank
  · exact SourceSizedQueries.rankSigned_unrankSigned classes nodeSize sized unique term size rank

section OriginalTable

variable [DecidableEq State] [Ord State] [DecidableEq Formula] [Ord (Label Formula)]

/-- The actual structural FTA validation supplies the reference route's finite carrier. -/
noncomputable def reference
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted table (fun _ _ => true))) : Except Unit (Api (Label Formula)) :=
  publicReference (SourceSizedStructuralKeys.input table root valid)

/-- Reference and fallback values have the original current raw language at every integer size. -/
theorem reference_signed_exact
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)))
    (api : Api (Label Formula)) (success : reference table root valid = .ok api)
    (size : Int) (term : Term (Label Formula)) :
    term ∈ api.terms size ↔
      Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver table) root term ∧
        (nodeSize term : Int) = size := by
  have exact := public_signed_exact formulas solver (SourceSizedStructuralKeys.input table root valid)
    api success size term
  rw [SourceSizedStructuralKeys.input_language table root valid
    (SourceConstraintEntryRaw.acceptsConstraint formulas solver) term] at exact
  exact exact

/-- Actual reference values are finite, complete, distinct, size ordered, and invertible. -/
theorem reference_correct
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
    (valid : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)))
    (api : Api (Label Formula)) (success : reference table root valid = .ok api) :
    let input := SourceSizedStructuralKeys.input table root valid
    (∀ size : Nat, SourceSizedReference.ClassEvaluation (equalityRows (sortedRows input)) (size + 1) size
      input.root (api.terms (size : Int))) ∧
    (∀ bound, (SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound).Nodup ∧
      (SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound).Pairwise
        (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ term, (∃ bound, term ∈ SourceSizedQueries.through (fun size : Nat => api.terms (size : Int)) bound) ↔
      Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver table) root term) ∧
    (∀ size rank term,
      (api.rank term).map (fun position => ((position.size : Int), (position.rank : Int))) = some (size, rank) ↔
        api.unrank size rank = some term) := by
  dsimp only
  refine ⟨fun size => public_finite _ api success size,
    fun bound => public_prefix_distinct_ordered _ api success bound, ?_,
    fun size rank term => public_signed_inverses _ api success size rank term⟩
  intro term
  have complete := public_complete formulas solver (SourceSizedStructuralKeys.input table root valid) api success term
  rw [SourceSizedStructuralKeys.input_language table root valid
    (SourceConstraintEntryRaw.acceptsConstraint formulas solver) term] at complete
  exact complete

end OriginalTable

end MicroCFTA.SourceSizedReferenceCurrent
