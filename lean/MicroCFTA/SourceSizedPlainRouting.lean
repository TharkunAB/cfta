import MicroCFTA.SourceSizedPlainQueries

/-!
# Complete plain-constraint branch with its computed fallback

The state worker uses the shared plain table when the scoped unambiguity
check passes. Otherwise it tries shared determinization. A failed helper
selects the actual reference class recurrence. All three paths give exact
queries after the scoped noConstraint check.

The global residual check and missing-state selection precede this worker.
The constrained equal-child branch, native storage, and original-input
total-work bound remain separate. No helper-success premise is required.
-/
namespace MicroCFTA.SourceSizedPlainRouting
open Language SourceSizedDecided SourceSizedFiniteKeys
open SourceObservations SourceSymbolicIndex SourceGuards

variable {State Formula : Type} [DecidableEq State] [Ord State]
  [DecidableEq Formula] [Ord (Label Formula)]

/-- Compute the actual sorted reference recurrence used after helper failure. -/
noncomputable def reference (table : Table State (Label Formula) (Constraint Formula))
    (initial : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (root : State) :
    SourceSizedDispatcher.Api (Label Formula) :=
  SourceSizedDispatcher.referenceApi
    (automaton (SourceSizedStructuralKeys.nativeSorted table initial success)
      SourceSizedEqualities.constraintHolds) root

omit [DecidableEq Formula] [Ord (Label Formula)] in
/-- The scoped plain check also clears the residual precheck at that root. -/
theorem residual_free (table : Table State (Label Formula) (Constraint Formula)) (root : State)
    (plain : SourceSizedGuardedDeterminization.plainCheck table root = true) :
    SourceSizedTrimGuards.residualScan (lookup table) (SourceDenseRows.keys table) root = false := by
  classical
  apply List.any_eq_false.mpr
  intro state _ bad
  obtain ⟨row, member, failed⟩ := List.any_eq_true.mp bad
  have neutral := SourceSizedScopedErasure.checked_constraint table root
    SourceSizedDispatcher.noConstraint plain state row member
  rw [neutral] at failed
  cases failed

variable [Std.TransOrd State] [Std.LawfulEqOrd State] [Ord (Sum State (List State))]

/-- Keep the plain table, actual shared determinization, and helper failure separate. -/
def tableClasses (table : Table State (Label Formula) (Constraint Formula)) (initial : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (root : State)
    (present : root ∈ SourceDenseRows.keys table) : Option (SourceSizedDispatcher.Api (Label Formula)) :=
  if SourceSizedScopedUnambiguity.unambiguousRows table root
      (SourceSizedSharedSorting.reroot_valid table initial root success present) then
    some (SourceSizedPlainQueries.api table initial success root)
  else (SourceSizedGuardedDeterminization.prepare table initial success).map (fun api => api root)

/-- A failed state helper uses the source reference API at that same state. -/
noncomputable def route (table : Table State (Label Formula) (Constraint Formula)) (initial : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (root : State)
    (present : root ∈ SourceDenseRows.keys table) : SourceSizedDispatcher.Api (Label Formula) :=
  (tableClasses table initial success root present).getD (reference table initial success root)

omit [Std.TransOrd State] [Std.LawfulEqOrd State] [Ord (Sum State (List State))] in
/-- The scoped noConstraint check gives the fallback its full original guarded meaning. -/
theorem reference_exact (table : Table State (Label Formula) (Constraint Formula))
    (initial root : State) (formulas : Formulas Formula) (solver : Entailment Formula)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (present : root ∈ SourceDenseRows.keys table)
    (plain : SourceSizedGuardedDeterminization.plainCheck table root = true) :
    SourceSizedApiLaws.Exact (reference table initial success root)
      (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  classical
  let valid := SourceSizedSharedSorting.reroot_valid table initial root success present
  let sorted := automaton (SourceSizedStructuralKeys.nativeSorted table initial success)
    SourceSizedEqualities.constraintHolds
  have permutation (state : State) :
      (sorted state).Perm (automaton (lookup table) SourceSizedEqualities.constraintHolds state) :=
    (SourceSizedStructuralKeys.nativeSorted_perm table initial success state).map
      (Row.edge SourceSizedEqualities.constraintHolds)
  refine SourceSizedApiLaws.reference sorted root _ ?_
  intro term
  exact (SourceCyclicAutomaton.permutation_language
    (automaton (lookup table) SourceSizedEqualities.constraintHolds) sorted permutation root term).trans
      ((SourceSizedScopedErasure.erasure_exact table root SourceSizedDispatcher.noConstraint
        SourceSizedEqualities.constraintHolds valid plain (fun _ => rfl) term).trans
          (SourceSizedScopedErasure.erasure_exact table root SourceSizedDispatcher.noConstraint
            (acceptsConstraint formulas solver) valid plain
            (fun candidate => SourceEqualityConstraintConstructors.top_true formulas solver candidate) term).symm)

/-- The scoped key/product check selects the shared plain count table. -/
theorem plain_shortcut (table : Table State (Label Formula) (Constraint Formula)) (initial root : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (present : root ∈ SourceDenseRows.keys table)
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root
      (SourceSizedSharedSorting.reroot_valid table initial root success present) = true) :
    tableClasses table initial success root present = some (SourceSizedPlainQueries.api table initial success root) := by
  simp only [tableClasses, passed, ↓reduceIte]

/-- A failed unambiguity check selects the actual shared determinization helper. -/
theorem determinization_after_failure (table : Table State (Label Formula) (Constraint Formula))
    (initial root : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (present : root ∈ SourceDenseRows.keys table)
    (failed : SourceSizedScopedUnambiguity.unambiguousRows table root
      (SourceSizedSharedSorting.reroot_valid table initial root success present) = false) :
    tableClasses table initial success root present =
      (SourceSizedGuardedDeterminization.prepare table initial success).map (fun api => api root) := by
  simp only [tableClasses, failed, Bool.false_eq_true, ↓reduceIte]

/-- All computed plain-constraint routes are exact, including a discovery-cap fallback. -/
theorem route_exact
    (table : Table State (Label Formula) (Constraint Formula)) (initial root : State)
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (present : root ∈ SourceDenseRows.keys table)
    (plain : SourceSizedGuardedDeterminization.plainCheck table root = true) :
    SourceSizedApiLaws.Exact (route table initial success root present)
      (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  by_cases unique : SourceSizedScopedUnambiguity.unambiguousRows table root
      (SourceSizedSharedSorting.reroot_valid table initial root success present) = true
  · rw [route, plain_shortcut table initial root success present unique]
    exact SourceSizedPlainQueries.queries_exact table initial root formulas solver success present plain unique
  · rw [route, tableClasses, ite_eq_right unique]
    cases prepared : SourceSizedGuardedDeterminization.prepare table initial success with
    | none =>
      exact reference_exact table initial root formulas solver success present plain
    | some api =>
      exact SourceSizedGuardedDeterminization.prepared_exact
        table initial root formulas solver success present plain api prepared

end MicroCFTA.SourceSizedPlainRouting
