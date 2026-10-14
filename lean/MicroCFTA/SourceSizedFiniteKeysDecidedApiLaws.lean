import MicroCFTA.SourceSizedFiniteKeysPublicDecided
import MicroCFTA.SourceSizedBoundedApiLaws

/-!
# Complete Sized query laws after actual bounded decisions

Successful bounded traces return the same canonical sequence as the
reference. The full query specification uses the original guarded language
with the signed bound. Finite per-call outcomes give finite execution and
retain the actual occurrence work and first error.
-/
namespace MicroCFTA.SourceSizedFiniteKeysPublic
open Language RecursiveSize SourceSizedFiniteKeys SourceSizedDecided SourceSizedPreprocessing

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State] [DecidableEq Symbol] [Ord Symbol]
    [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (evaluates : Payload × Term Symbol → Nat → Guards.Verdict → Prop)
    (holds : Payload → Term Symbol → Bool)
    (adequate : SourceSizedDecidedOperational.Adequate evaluates (fun pair => holds pair.1 pair.2))
    (bound : Int)

include adequate

/-- Every successful actual bounded trace returns one complete exact public query record. -/
theorem decided_exact
    (output : SourceSizedDecidedTable.Table (SourceDenseRows.Member (SourceDenseRows.keys table)) (Term Symbol))
    (work : Nat) (run : DecidedRun table root valid evaluates bound (.ok output) work) :
    SourceSizedApiLaws.Exact (SourceSizedBoundedApiLaws.fromClasses (output (input table root valid).root))
      (fun term => Accepts (automaton (lookup table) holds) root term ∧ (nodeSize term : Int) ≤ bound) := by
  have facts := decided_correct table root valid evaluates holds adequate bound output work run
  exact SourceSizedBoundedApiLaws.exact (automaton (nativeSorted table root valid) holds) root bound
    (output (input table root valid).root) (Accepts (automaton (lookup table) holds) root) facts.2.1 facts.1

/-- Finite actual decisions give a finite source outcome and all exact laws on successful output. -/
theorem decided_complete_exact (completed : SourceSizedDecidedOperational.Terminates evaluates) :
    ∃ result work, DecidedRun table root valid evaluates bound result work ∧
      ∀ output, result = .ok output →
        SourceSizedApiLaws.Exact (SourceSizedBoundedApiLaws.fromClasses (output (input table root valid).root))
          (fun term => Accepts (automaton (lookup table) holds) root term ∧ (nodeSize term : Int) ≤ bound) := by
  obtain ⟨result, work, run⟩ := decided_finite table root valid evaluates completed bound
  refine ⟨result, work, run, ?_⟩
  intro output success
  subst result
  exact decided_exact table root valid evaluates holds adequate bound output work run

end MicroCFTA.SourceSizedFiniteKeysPublic
