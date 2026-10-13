import MicroCFTA.SourceSizedFiniteKeysPublicDecided
import MicroCFTA.SourceSolverNamePublic

/-!
# Encoded liquid Sized queries on finite validated row maps

The logical language uses original names and original raw constraints.
The actual callback uses the injective encoded solver preflight. External
completion and Sat/Unsat correctness remain explicit per-call contracts.
Unknown and raised failures remain different finite outcomes.
-/
namespace MicroCFTA.SourceSizedFiniteKeysPublic
open Language RecursiveSize SourceSizedFiniteKeys SourceSizedDecided
open SourceObservations SourceSizedPreprocessing SourceSizedLiquidProgram SolverAdapter

variable {State : Type} [DecidableEq State] [Ord State] [Ord (Label FullSyntax.Formula)]

/-- A complete source liquid table retains raw names, constraints, and original states. -/
abbrev LiquidTable (State : Type) :=
  SourceSizedFiniteKeys.Table State (Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula)

/-- The actual encoded public trace runs on exactly the table-key carrier supplied by validation. -/
abbrev EncodedRun (table : LiquidTable State) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (bound : Int)
    (result : Except Failure (Except (SourceSymbolicIndex.Constraint FullSyntax.Formula × Term (Label FullSyntax.Formula))
      (SourceSizedDecidedTable.Table (SourceDenseRows.Member (SourceDenseRows.keys table)) (Term (Label FullSyntax.Formula))))) (work : Nat) : Prop :=
  SourceSizedLiquidExecutionPublic.PublicRun (input table root valid)
    (SourceSolverNamePublic.Call given assumptions milliseconds check) bound result work

omit [Ord (Label FullSyntax.Formula)] in
/-- The independent quantified liquid language is unchanged by validation-derived restriction. -/
theorem logical_language (table : LiquidTable State) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (meaning : Query → Prop) (term : Term (Label FullSyntax.Formula)) :
    SourceSizedLiquidAmbientPublic.Accepts meaning (input table root valid).rows (input table root valid).root term ↔
      SourceSizedLiquidAmbientPublic.Accepts meaning (lookup table) root term := by
  rw [← SourceSizedLiquidAmbientPublic.accepts_iff, ← SourceSizedLiquidAmbientPublic.accepts_iff, input_language]

/-- Encoded solver success gives exact original liquid terms, source order, coverage, and both inverse laws. -/
theorem encoded_correct [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)]
    (table : LiquidTable State) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (model : FormulaLowering.Model Value) (given : List Declaration) (assumptions : List FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response)
    (bound : Int)
    (output : SourceSizedDecidedTable.Table (SourceDenseRows.Member (SourceDenseRows.keys table)) (Term (Label FullSyntax.Formula)))
    (work : Nat) (run : EncodedRun table root valid given assumptions milliseconds check bound (.ok (.ok output)) work) :
    let meaning := SourceSizedLiquidAmbient.Meaning model given assumptions
    let terms := output (input table root valid).root
    (∀ size term, term ∈ terms size ↔ SourceSizedLiquidAmbientPublic.Accepts meaning (lookup table) root term ∧
      nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, terms size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (nativeSorted table root valid) (SourceSizedLiquidAmbientAdequacy.truth meaning)) size root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through terms throughSize).Nodup ∧
      (SourceSizedQueries.through terms throughSize).Pairwise (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ throughSize term, term ∈ SourceSizedQueries.through terms throughSize ↔
      SourceSizedLiquidAmbientPublic.Accepts meaning (lookup table) root term ∧
        (nodeSize term : Int) ≤ bound ∧ nodeSize term ≤ throughSize) ∧
    (∀ term size rank, SourceSizedQueries.rankSigned terms nodeSize term = some (size, rank) ↔
      SourceSizedQueries.unrankSigned terms size rank = some term) := by
  dsimp only
  obtain ⟨members, order, enumeration, inverses⟩ := SourceSolverNamePublic.public_correct model given assumptions milliseconds check correct
    (input table root valid) bound output work run
  have membership : ∀ size term, term ∈ output (input table root valid).root size ↔
      SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAmbient.Meaning model given assumptions) (lookup table) root term ∧
        nodeSize term = size ∧ (size : Int) ≤ bound := by
    intro size term
    rw [members, logical_language]
  refine ⟨membership, ?_, enumeration, ?_, inverses⟩
  · intro size
    have sorted := sorted_classes_exact table root valid
      (SourceSizedLiquidAmbientAdequacy.truth (SourceSizedLiquidAmbient.Meaning model given assumptions)) (input table root valid).root size
    change SourceSizedReference.classes _ size (input table root valid).root = SourceSizedReference.classes _ size root at sorted
    rw [order, sorted]
  · intro throughSize term
    rw [SourceSizedQueries.mem_prefix]
    constructor
    · rintro ⟨size, below, present⟩
      obtain ⟨accepted, sized, bounded⟩ := (membership size term).mp present
      exact ⟨accepted, by omega, by omega⟩
    · rintro ⟨accepted, bounded, below⟩
      exact ⟨nodeSize term, below, (membership _ term).mpr ⟨accepted, rfl, bounded⟩⟩

/-- Every signed bound has a finite encoded outcome if every external attempt finishes. -/
theorem encoded_finite (table : LiquidTable State) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (completed : ∀ request, ∃ work attempt, check request work attempt)
    (bound : Int) : ∃ result work, EncodedRun table root valid given assumptions milliseconds check bound result work :=
  SourceSolverNamePublic.public_finite (input table root valid) given assumptions milliseconds check completed bound

end MicroCFTA.SourceSizedFiniteKeysPublic
