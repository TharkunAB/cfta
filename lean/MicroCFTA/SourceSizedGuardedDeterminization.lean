import MicroCFTA.SourceSizedScopedQueries
import MicroCFTA.SourceEqualityConstraintConstructors

/-!
# The shared Sized determinization branch

The source runs discovery with limit 1024 on all erased original rows.
Successful preparation stores one canonical table for every query state.
The actual noConstraint check on the query's trimmed rows gives exact
queries for the original guarded language at that state.

Failure is exactly the source discovery limit. The full Sized routing
must then select its reference fallback. This module does not establish
the complete dispatcher, native storage, or an original-input work bound.
-/
namespace MicroCFTA.SourceSizedGuardedDeterminization
open Language SourceSizedFiniteKeys SourceSizedDecided Std
open SourceObservations SourceSymbolicIndex SourceGuards

variable {State Formula : Type} [DecidableEq State] [Ord State]
  [TransOrd State] [LawfulEqOrd State] [Ord (Sum State (List State))]
  [DecidableEq Formula] [Ord (Label Formula)]

/-- Use the source noConstraint comparison on the query's structurally trimmed rows. -/
noncomputable def plainCheck (table : Table State (Label Formula) (Constraint Formula))
    (root : State) : Bool := by
  classical
  exact SourceSizedScopedErasure.plainCheck table root SourceSizedDispatcher.noConstraint

/-- Compute the one shared determinized query table at the source's fixed limit. -/
def prepare (table : Table State (Label Formula) (Constraint Formula)) (initial : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) : Option (State → SourceSizedDispatcher.Api (Label Formula)) :=
  match returned : SourceSizedDeterminizationTableInput.compile 1024 table with
  | .ready known choices => some fun root =>
      SourceSizedDispatcher.optimizedApi
        (automaton (SourceSizedDeterminizationTableInput.sortedRows
          1024 table initial success known choices returned) (fun _ _ => true)) (.inl root)
  | .limitExceeded | .exhausted => none

/-- Only the actual discovery limit can reject shared preparation. -/
theorem prepare_none_iff (table : Table State (Label Formula) (Constraint Formula)) (initial : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    prepare table initial success = none ↔
      SourceSizedDeterminizationTableInput.compile 1024 table = .limitExceeded := by
  unfold prepare
  split
  · simp_all
  · simp_all
  · rename_i impossible
    exact (SourceSizedDeterminizationTableInput.compile_terminal 1024 table impossible).elim

/-- Returned discovery and the actual scoped source check give exact guarded queries. -/
theorem queries_exact (table : Table State (Label Formula) (Constraint Formula))
    (initial root : State) (formulas : Formulas Formula) (solver : Entailment Formula)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (present : root ∈ SourceDenseRows.keys table) (passed : plainCheck table root = true)
    (known : List (List State))
    (choices : List (SourceSizedDeterminizationKernel.Choice State (Label Formula)))
    (returned : SourceSizedDeterminizationTableInput.compile 1024 table = .ready known choices) :
    SourceSizedApiLaws.Exact
      (SourceSizedDispatcher.optimizedApi
        (automaton (SourceSizedDeterminizationTableInput.sortedRows
          1024 table initial success known choices returned) (fun _ _ => true)) (.inl root))
      (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  classical
  exact SourceSizedScopedQueries.determinized_exact 1024 table initial root
    SourceSizedDispatcher.noConstraint (acceptsConstraint formulas solver) success present passed
    (fun term => SourceEqualityConstraintConstructors.top_true formulas solver term) known choices returned

/-- Successful computed preparation supplies exact queries without a completed-table premise. -/
theorem prepared_exact (table : Table State (Label Formula) (Constraint Formula))
    (initial root : State) (formulas : Formulas Formula) (solver : Entailment Formula)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (present : root ∈ SourceDenseRows.keys table) (passed : plainCheck table root = true)
    (api : State → SourceSizedDispatcher.Api (Label Formula))
    (prepared : prepare table initial success = some api) :
    SourceSizedApiLaws.Exact (api root)
      (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  unfold prepare at prepared
  split at prepared
  · rename_i known choices returned
    cases Option.some.inj prepared
    exact queries_exact table initial root formulas solver success present passed known choices returned
  · simp at prepared
  · simp at prepared

end MicroCFTA.SourceSizedGuardedDeterminization
