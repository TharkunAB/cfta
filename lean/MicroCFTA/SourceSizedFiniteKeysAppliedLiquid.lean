import MicroCFTA.SourceSizedFiniteKeysNativeLiquid
import MicroCFTA.SourceSolverAppliedPublic
import MicroCFTA.SourceSizedBoundedApiLaws

/-!
# Current inferred-sort execution on the original finite row map

The raw trim and state folds use the original map keys and constraints.
The callback uses the current encoded declaration preparation. Exact
readback retains source classes, size order, coverage, and both rank laws.
-/
namespace MicroCFTA.SourceSizedFiniteKeysAppliedLiquid
open Language RecursiveSize SourceObservations SourceSizedDecided
open SourceSizedFiniteKeys SourceSizedFiniteKeysPublic SourceSizedLiquidProgram SolverAdapter

variable {State : Type} [DecidableEq State] [Ord State] [Ord (Label FullSyntax.Formula)]
  [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)]
  (table : LiquidTable State) (root : State)
  (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
    .ok (interpreted table (fun _ _ => true)))

/-- Run current encoded queries in the actual original-state raw fold. -/
abbrev NativeRun (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (bound : Int)
    (result : SourceSizedLiquidExecution.Outcome
      (SourceSymbolicIndex.Constraint FullSyntax.Formula × Term (Label FullSyntax.Formula))
      (SourceSizedDecidedTable.Table State (Term (Label FullSyntax.Formula)))) (work : Nat) : Prop :=
  SourceSizedFiniteKeysNativeLiquid.NativeRun table root valid
    (SourceSolverAppliedPublic.Call given assumptions milliseconds check) bound result work

omit [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)] in
/-- Finite current external attempts give a finite original-state outcome. -/
theorem encoded_finite (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (bound : Int) :
    ∃ result work, NativeRun table root valid given assumptions milliseconds check bound result work :=
  SourceSizedFiniteKeysNativeLiquid.native_finite table root valid _
    (SourceSolverAppliedPublic.call_finite given assumptions milliseconds check completed) bound

/-- Current raw execution gives exact original terms, source order, coverage, and both rank laws. -/
theorem encoded_correct (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (bound : Int) (output : SourceSizedDecidedTable.Table State (Term (Label FullSyntax.Formula))) (work : Nat)
    (run : NativeRun table root valid given assumptions milliseconds check bound (.ok (.ok output)) work) :
    let meaning := SourceSizedLiquidAppliedAmbient.Meaning model given assumptions
    let terms := output root
    (∀ size term, term ∈ terms size ↔ SourceSizedLiquidAmbientPublic.Accepts meaning (lookup table) root term ∧
      nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, terms size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (nativeSorted table root valid)
        (SourceSizedLiquidAmbientAdequacy.truth meaning)) size root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through terms throughSize).Nodup ∧
      (SourceSizedQueries.through terms throughSize).Pairwise (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ throughSize term, term ∈ SourceSizedQueries.through terms throughSize ↔
      SourceSizedLiquidAmbientPublic.Accepts meaning (lookup table) root term ∧
        (nodeSize term : Int) ≤ bound ∧ nodeSize term ≤ throughSize) ∧
    (∀ term size rank, SourceSizedQueries.rankSigned terms nodeSize term = some (size, rank) ↔
      SourceSizedQueries.unrankSigned terms size rank = some term) := by
  dsimp only
  have transferred := SourceSizedFiniteKeysNativeLiquid.trace_readback table root valid _ bound _ work run
  obtain ⟨members, order, enumeration, inverses⟩ := SourceSolverAppliedPublic.public_correct model given assumptions
    milliseconds check correct (input table root valid) bound
    (SourceSizedFiniteKeysExecution.pull Subtype.val output) work transferred
  change ∀ size term, term ∈ output root size ↔ _ at members
  change ∀ size, output root size = _ at order
  have membership : ∀ size term, term ∈ output root size ↔
      SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAppliedAmbient.Meaning model given assumptions)
        (lookup table) root term ∧ nodeSize term = size ∧ (size : Int) ≤ bound := by
    intro size term
    rw [members, logical_language]
  refine ⟨membership, ?_, enumeration, ?_, inverses⟩
  · intro size
    have sorted := sorted_classes_exact table root valid
      (SourceSizedLiquidAmbientAdequacy.truth (SourceSizedLiquidAppliedAmbient.Meaning model given assumptions))
      (input table root valid).root size
    change SourceSizedReference.classes _ size (input table root valid).root =
      SourceSizedReference.classes _ size root at sorted
    rw [order, sorted]
  · intro throughSize term
    rw [SourceSizedQueries.mem_prefix]
    constructor
    · rintro ⟨size, below, present⟩
      obtain ⟨accepted, sized, bounded⟩ := (membership size term).mp present
      exact ⟨accepted, by omega, by omega⟩
    · rintro ⟨accepted, bounded, below⟩
      exact ⟨nodeSize term, below, (membership _ term).mpr ⟨accepted, rfl, bounded⟩⟩

/-- The current raw fold gives all exact API queries at the original bounded language. -/
theorem encoded_exact (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (bound : Int) (output : SourceSizedDecidedTable.Table State (Term (Label FullSyntax.Formula))) (work : Nat)
    (run : NativeRun table root valid given assumptions milliseconds check bound (.ok (.ok output)) work) :
    SourceSizedApiLaws.Exact (SourceSizedBoundedApiLaws.fromClasses (output root))
      (fun term => SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAppliedAmbient.Meaning model given assumptions)
        (lookup table) root term ∧ (nodeSize term : Int) ≤ bound) := by
  have facts := encoded_correct table root valid model given assumptions milliseconds check correct bound output work run
  exact SourceSizedBoundedApiLaws.exact
    (automaton (nativeSorted table root valid)
      (SourceSizedLiquidAmbientAdequacy.truth (SourceSizedLiquidAppliedAmbient.Meaning model given assumptions)))
    root bound (output root)
    (SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAppliedAmbient.Meaning model given assumptions) (lookup table) root)
    facts.2.1 facts.1

/-- Finite current external attempts give a finite raw result and the exact API on success. -/
theorem encoded_complete_exact (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (bound : Int) :
    ∃ result work, NativeRun table root valid given assumptions milliseconds check bound result work ∧
      ∀ output, result = .ok (.ok output) →
        SourceSizedApiLaws.Exact (SourceSizedBoundedApiLaws.fromClasses (output root))
          (fun term => SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAppliedAmbient.Meaning model given assumptions)
            (lookup table) root term ∧ (nodeSize term : Int) ≤ bound) := by
  obtain ⟨result, work, run⟩ := encoded_finite table root valid given assumptions milliseconds check completed bound
  refine ⟨result, work, run, ?_⟩
  intro output success
  subst result
  exact encoded_exact table root valid model given assumptions milliseconds check correct bound output work run

end MicroCFTA.SourceSizedFiniteKeysAppliedLiquid
