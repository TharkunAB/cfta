import MicroCFTA.SourceSizedFiniteKeysNativeLiquid
import MicroCFTA.SourceSizedBoundedApiLaws

/-!
# Complete Sized queries after actual encoded solver execution

The successful raw fold gives the common exact query specification at the
independent ambient language. Finite external attempts give finite outcomes
with the actual work. Unknown and raised failures retain separate channels.
-/
namespace MicroCFTA.SourceSizedFiniteKeysNativeLiquid
open Language RecursiveSize SourceObservations SourceSizedDecided SourceSizedFiniteKeys SourceSizedFiniteKeysPublic
open SourceSizedLiquidProgram SolverAdapter

variable {State : Type} [DecidableEq State] [Ord State] [Ord (Label FullSyntax.Formula)]
    [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)]
    (table : LiquidTable State) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (model : FormulaLowering.Model Value) (given : List Declaration) (assumptions : List FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response)
    (bound : Int)

include correct

/-- Every successful encoded raw fold satisfies all exact queries at the original bounded ambient language. -/
theorem encoded_exact (output : SourceSizedDecidedTable.Table State (Term (Label FullSyntax.Formula)))
    (work : Nat) (run : NativeRun table root valid (SourceSolverNamePublic.Call given assumptions milliseconds check)
      bound (.ok (.ok output)) work) :
    SourceSizedApiLaws.Exact (SourceSizedBoundedApiLaws.fromClasses (output root))
      (fun term => SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAmbient.Meaning model given assumptions)
        (lookup table) root term ∧ (nodeSize term : Int) ≤ bound) := by
  have facts := encoded_correct table root valid model given assumptions milliseconds check correct bound output work run
  exact SourceSizedBoundedApiLaws.exact
    (automaton (nativeSorted table root valid)
      (SourceSizedLiquidAmbientAdequacy.truth (SourceSizedLiquidAmbient.Meaning model given assumptions)))
    root bound (output root)
    (SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAmbient.Meaning model given assumptions) (lookup table) root)
    facts.2.1 facts.1

/-- Finite external attempts give a finite actual raw outcome and the complete exact API on success. -/
theorem encoded_complete_exact (completed : ∀ request, ∃ work attempt, check request work attempt) :
    ∃ result work, NativeRun table root valid (SourceSolverNamePublic.Call given assumptions milliseconds check) bound result work ∧
      ∀ output, result = .ok (.ok output) →
        SourceSizedApiLaws.Exact (SourceSizedBoundedApiLaws.fromClasses (output root))
          (fun term => SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAmbient.Meaning model given assumptions)
            (lookup table) root term ∧ (nodeSize term : Int) ≤ bound) := by
  obtain ⟨result, work, run⟩ := encoded_finite table root valid given assumptions milliseconds check completed bound
  refine ⟨result, work, run, ?_⟩
  intro output success
  subst result
  exact encoded_exact table root valid model given assumptions milliseconds check correct bound output work run

end MicroCFTA.SourceSizedFiniteKeysNativeLiquid
