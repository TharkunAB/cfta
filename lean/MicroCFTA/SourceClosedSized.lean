import MicroCFTA.SourceFreshOrdinarySizedEntryCorrect
import MicroCFTA.SourceFreshOrdinaryLiquidEntryCorrect
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

/-!
# Complete exact Sized queries from original closed source expressions

The existing construction theorem derives the actual finished value and
cache. Staged conversion then returns an exact source error or complete
queries at the expression's independent guarded least language.
-/
namespace MicroCFTA.SourceClosedSized
open Cache Language RecursiveSize InternedConstructorTemplates
open SourceObservations SourceSymbolicIndex SourceGuards SolverAdapter SourceSizedLiquidProgram

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "Api" => SourceSizedDispatcher.Api Symbol

variable [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Original checked syntax derives complete reference and optimized execution at the same exact least language. -/
theorem reference_and_dispatch (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun constraint : SourceSymbolicIndex.Constraint FullSyntax.Formula =>
        SourceCompactGuards.ActiveOption constraint.equalities) expression)
    (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula) :
    ∃ value state result final,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      SourceFreshOrdinarySizedEntry.Execution false value state result final ∧
      SourceFreshOrdinarySizedEntry.Execution true value state result final ∧
      ∀ api, result = .ok (.ok api) →
        SourceSizedApiLaws.Exact api (InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression) := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  obtain ⟨result, final, reference, dispatch, queries⟩ :=
    SourceFreshOrdinarySizedEntry.constructed_complete value expression state built annotations formulas solver
  refine ⟨value, state, result, final, built, reference, dispatch, ?_⟩
  intro api success
  have exactQueries := queries api success (fun _ _ => False)
  rw [InternedGuardedExecution.closed_language expression value state built (acceptsConstraint formulas solver)] at exactQueries
  exact exactQueries

/-- Original syntax and finite correct external attempts derive complete exact bounded encoded queries. -/
theorem solver_decided (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (model : FormulaLowering.Model ModelValue) (given : List Declaration) (assumptions : List FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response)
    (bound : Int) :
    ∃ value state result final,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      SourceFreshOrdinaryLiquidEntry.Execution given assumptions milliseconds check bound value state result final ∧
      ∀ api, result = .ok (.ok (.ok api)) →
        SourceSizedApiLaws.Exact api (fun term => InternedGuardedSyntax.evaluate
          (SourceSizedLiquidAmbientAdequacy.truth (SourceSizedLiquidAmbient.Meaning model given assumptions)) [] expression term ∧
          (nodeSize term : Int) ≤ bound) := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  obtain ⟨result, final, actual, queries⟩ := SourceFreshOrdinaryLiquidEntry.constructed_complete
    given assumptions milliseconds check bound value expression state built completed model correct
  refine ⟨value, state, result, final, built, actual, ?_⟩
  intro api success
  have exactQueries := queries api success (fun _ _ => False)
  rw [InternedGuardedExecution.closed_language expression value state built] at exactQueries
  exact exactQueries

end MicroCFTA.SourceClosedSized
