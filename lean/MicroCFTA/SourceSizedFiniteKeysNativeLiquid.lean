import MicroCFTA.SourceSizedFiniteKeysOperational
import MicroCFTA.SourceSizedFiniteKeysTrim
import MicroCFTA.SourceSizedFiniteKeysPublicLiquid

/-!
# Encoded liquid execution on the actual original-state finite map

The state fold uses raw trim keys and dense-sorted original rows. This is
not a finite-state-type assumption. Exact trace readback transfers every
outcome, and the public theorem gives the original independent language.
-/
namespace MicroCFTA.SourceSizedFiniteKeysNativeLiquid
open Language SourceObservations SourceSizedDecided SourceSizedDecidedExecution
open SourceSizedFiniteKeys SourceSizedFiniteKeysPublic SourceSizedLiquidProgram SolverAdapter

/-- Restrict successful tables while retaining both original stopping channels. -/
def mapOutput (encode : Source → Target)
    (result : SourceSizedLiquidExecution.Outcome Item (SourceSizedDecidedTable.Table Target Value)) :
    SourceSizedLiquidExecution.Outcome Item (SourceSizedDecidedTable.Table Source Value) :=
  result.map (fun inner => inner.map (SourceSizedFiniteKeysExecution.pull encode))

/-- Outcome restriction preserves the exact encoded Unknown or raised failure. -/
theorem encode_mapOutput (encode : Source → Target)
    (result : SourceSizedLiquidExecution.Outcome Item (SourceSizedDecidedTable.Table Target Value)) :
    SourceSizedLiquidExecution.encode (mapOutput encode result) =
      (SourceSizedLiquidExecution.encode result).map (SourceSizedFiniteKeysExecution.pull encode) := by
  cases result with
  | error _ => rfl
  | ok inner => cases inner <;> rfl

variable {State : Type} [DecidableEq State] [Ord State] [Ord (Label FullSyntax.Formula)]
  [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)]
  (table : LiquidTable State) (root : State)
  (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
    .ok (interpreted table (fun _ _ => true)))

/-- Execute original raw rows at the actual root-preserving raw trim inventory. -/
abbrev NativeRun (oracle : Query → Nat → Result → Prop) (bound : Int)
    (result : SourceSizedLiquidExecution.Outcome (SourceSymbolicIndex.Constraint FullSyntax.Formula × Term (Label FullSyntax.Formula))
      (SourceSizedDecidedTable.Table State (Term (Label FullSyntax.Formula)))) (work : Nat) : Prop :=
  SizesRun (SourceSizedLiquidExecution.ClassRun (nativeSorted table root valid)
    (SourceSizedLiquidExecutionPublic.Evaluation oracle))
    (SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) (fun _ _ => true)) root)
    bound.toNat (SourceSizedLiquidExecution.encode result) work

/-- Every actual raw trace is the corresponding finite-key public trace with the same work. -/
theorem trace_readback (oracle : Query → Nat → Result → Prop) (bound : Int) (result work)
    (run : NativeRun table root valid oracle bound result work) :
    SourceSizedLiquidExecutionPublic.PublicRun (input table root valid) oracle bound
      (mapOutput Subtype.val result) work := by
  unfold NativeRun at run
  rw [←SourceSizedFiniteKeysTrim.reached_readback table root valid (fun _ _ => true)] at run
  have transferred := SourceSizedFiniteKeysOperational.native_public table root valid
    (SourceSizedLiquidExecutionPublic.Evaluation oracle) bound.toNat _ work run
  unfold SourceSizedLiquidExecutionPublic.PublicRun
  rw [encode_mapOutput]
  exact transferred

omit [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)] in
/-- Finite query occurrences give finite original-state executions, including all error outcomes. -/
theorem native_finite (oracle : Query → Nat → Result → Prop)
    (completed : ∀ query, ∃ work result, oracle query work result) (bound : Int) :
    ∃ result work, NativeRun table root valid oracle bound result work := by
  have evaluations : ∀ pair, ∃ work result, SourceSizedLiquidExecutionPublic.Evaluation oracle pair work result :=
    fun pair => SourceSizedLiquidProgram.finite_execution oracle completed
      (SourceSizedLiquidEvaluation.constraintProgram pair.1 pair.2)
  obtain ⟨result, work, run⟩ := SourceSizedLiquidExecution.sizes_finite (nativeSorted table root valid)
    (SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) (fun _ _ => true)) root)
    (SourceSizedLiquidExecutionPublic.Evaluation oracle) evaluations bound.toNat
  exact ⟨SourceSizedLiquidExecution.decode result, work,
    by simpa only [NativeRun, SourceSizedLiquidExecution.encode_decode] using run⟩

omit [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)] in
/-- Finite actual encoded external attempts suffice for the original raw bounded source execution. -/
theorem encoded_finite (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (completed : ∀ request, ∃ work attempt, check request work attempt)
    (bound : Int) :
    ∃ result work, NativeRun table root valid (SourceSolverNamePublic.Call given assumptions milliseconds check)
      bound result work :=
  native_finite table root valid _ (SourceSolverNamePublic.call_finite given assumptions milliseconds check completed) bound

/-- The actual raw fold has exact guarded terms, canonical source order, coverage, and both rank laws. -/
theorem encoded_correct (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response)
    (bound : Int) (output : SourceSizedDecidedTable.Table State (Term (Label FullSyntax.Formula))) (work : Nat)
    (run : NativeRun table root valid (SourceSolverNamePublic.Call given assumptions milliseconds check)
      bound (.ok (.ok output)) work) :
    let meaning := SourceSizedLiquidAmbient.Meaning model given assumptions
    let terms := output root
    (∀ size term, term ∈ terms size ↔ SourceSizedLiquidAmbientPublic.Accepts meaning (lookup table) root term ∧
      RecursiveSize.nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, terms size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (nativeSorted table root valid) (SourceSizedLiquidAmbientAdequacy.truth meaning)) size root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through terms throughSize).Nodup ∧
      (SourceSizedQueries.through terms throughSize).Pairwise
        (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second)) ∧
    (∀ throughSize term, term ∈ SourceSizedQueries.through terms throughSize ↔
      SourceSizedLiquidAmbientPublic.Accepts meaning (lookup table) root term ∧
        (RecursiveSize.nodeSize term : Int) ≤ bound ∧ RecursiveSize.nodeSize term ≤ throughSize) ∧
    (∀ term size rank, SourceSizedQueries.rankSigned terms RecursiveSize.nodeSize term = some (size, rank) ↔
      SourceSizedQueries.unrankSigned terms size rank = some term) := by
  have transferred := trace_readback table root valid _ bound _ work run
  exact SourceSizedFiniteKeysPublic.encoded_correct table root valid model given assumptions milliseconds check correct
    bound (SourceSizedFiniteKeysExecution.pull Subtype.val output) work transferred

end MicroCFTA.SourceSizedFiniteKeysNativeLiquid
