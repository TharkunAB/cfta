import MicroCFTA.SourceSizedLiquidExecution

/-!
# Public bounded liquid outcomes

The outer error is a solver IO exception. The returned result contains
either GuardUnknown or the bounded table. Finite external completions can
include exceptions. Successful traces use the existing complete language,
canonical order, and rank inverse theorem without a stable-reply premise.
-/

namespace MicroCFTA.SourceSizedLiquidExecutionPublic

open FullSyntax SourceObservations Language SolverAdapter
open SourceSizedPreprocessing SourceSizedDecidedPublic SourceSizedDecided
open SourceSizedDecidedTable SourceSizedDecidedExecution SourceSizedLiquidProgram
open SourceSizedLiquidExecution SourceSizedLiquidAdequacy

/-- Each complete candidate constraint executes its actual ordered query program. -/
def Evaluation (oracle : Query → Nat → SolverAdapter.Result → Prop)
    (pair : SourceSymbolicIndex.Constraint Formula × Term (Label Formula))
    (work : Nat) (result : SolverAdapter.Result) : Prop :=
  Run oracle (SourceSizedLiquidEvaluation.constraintProgram pair.1 pair.2) result work

/-- The public fold preserves IO exceptions outside the returned Sized result. -/
abbrev PublicRun [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (oracle : Query → Nat → SolverAdapter.Result → Prop) (bound : Int)
    (result : Outcome (SourceSymbolicIndex.Constraint Formula × Term (Label Formula))
      (Table State (Term (Label Formula)))) (work : Nat) : Prop :=
  SizesRun (SourceSizedLiquidExecution.ClassRun (sortedRows input) (Evaluation oracle))
    (reached input) bound.toNat (encode result) work

/-- Every public bound has a finite result if every query occurrence can finish. -/
theorem public_finite [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (oracle : Query → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ query, ∃ work result, oracle query work result) (bound : Int) :
    ∃ result work, PublicRun input oracle bound result work := by
  have evaluations : ∀ pair, ∃ work result, Evaluation oracle pair work result :=
    fun pair => SourceSizedLiquidProgram.finite_execution oracle completed
      (SourceSizedLiquidEvaluation.constraintProgram pair.1 pair.2)
  obtain ⟨result, work, executed⟩ := SourceSizedLiquidExecution.sizes_finite
    (sortedRows input) (reached input) (Evaluation oracle) evaluations bound.toNat
  exact ⟨decode result, work, by simpa only [PublicRun, encode_decode] using executed⟩

/-- Actual completed solver attempts suffice, including interruption and protocol exceptions. -/
theorem adapter_finite [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (given : List Declaration) (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (bound : Int) :
    ∃ result work, PublicRun input (SourceSizedLiquidAdapter.Call given milliseconds check) bound result work :=
  public_finite input _ (SourceSizedLiquidAdapter.call_finite given milliseconds check completed) bound

/-- Nonpositive bounds return an empty table with no candidate or solver evaluation. -/
theorem public_nonpositive [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (oracle : Query → Nat → SolverAdapter.Result → Prop) (bound : Int) (nonpositive : bound ≤ 0) :
    PublicRun input oracle bound (.ok (.ok (fun _ _ => []))) 0 := by
  unfold PublicRun
  rw [Int.toNat_of_nonpos nonpositive]
  exact .zero

/-- Successful complete outcomes transfer to the existing public trace at the same finite work. -/
theorem public_success [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (oracle : Query → Nat → SolverAdapter.Result → Prop) (bound : Int)
    (output : Table State (Term (Label Formula))) (work : Nat)
    (run : PublicRun input oracle bound (.ok (.ok output)) work) :
    SizesRun (SourceSizedDecided.ClassRun (sortedRows input) (Evaluates oracle))
      (reached input) bound.toNat (.ok output) work :=
  SourceSizedLiquidExecution.sizes_success (sortedRows input) (reached input) (Evaluation oracle) run output rfl

/-- The actual adapter success is exactly the previously proved public SizedRun. -/
theorem adapter_success [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (given : List Declaration) (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (bound : Int) (output : Table State (Term (Label Formula))) (work : Nat)
    (run : PublicRun input (SourceSizedLiquidAdapter.Call given milliseconds check) bound (.ok (.ok output)) work) :
    SourceSizedLiquidPublic.SizedRun input given milliseconds check bound (.ok output) work :=
  public_success input _ bound output work run

/-- Public failure retains successful prefixes and the first exact stopping evaluation. -/
theorem public_first_stop [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (oracle : Query → Nat → SolverAdapter.Result → Prop) (bound : Int)
    (bad : Halt (SourceSymbolicIndex.Constraint Formula × Term (Label Formula))) (work : Nat)
    (run : PublicRun input oracle bound (decode (.error bad)) work) :
    ∃ earlier smaller sizeWork, earlier < bound.toNat ∧
      SizesRun (SourceSizedDecided.ClassRun (sortedRows input) (Evaluates oracle))
        (reached input) earlier (.ok smaller) sizeWork ∧
      ∃ beforeStates state afterStates intermediate stateWork,
        reached input = beforeStates ++ state :: afterStates ∧
        StatesRun (SourceSizedDecided.ClassRun (sortedRows input) (Evaluates oracle)) smaller (earlier + 1)
          beforeStates smaller (.ok intermediate) stateWork ∧
        ∃ beforeTerms item afterTerms accepted termWork stopWork,
          pairs (sortedRows input) smaller (earlier + 1) state = beforeTerms ++ item :: afterTerms ∧
          SourceSizedDecidedFilter.Run (Evaluates oracle) beforeTerms (.ok accepted) termWork ∧
          Caused (Evaluation oracle) bad item stopWork := by
  unfold PublicRun at run
  rw [encode_decode] at run
  exact sizes_first_stop (sortedRows input) (reached input) (Evaluation oracle) run bad rfl

/-- A whole-query IO exception originates in an actual query occurrence, unchanged. -/
theorem public_exception_origin [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (oracle : Query → Nat → SolverAdapter.Result → Prop) (bound : Int)
    (failure : SolverAdapter.Failure) (work : Nat)
    (run : PublicRun input oracle bound (.error failure) work) :
    ∃ query queryWork, oracle query queryWork (.raised failure) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, caused⟩ :=
    public_first_stop input oracle bound (.raised failure) work run
  exact SourceSizedLiquidProgram.raised_origin oracle caused failure rfl

/-- Returned GuardUnknown identifies a complete constraint evaluation, not an IO exception. -/
theorem public_unknown_origin [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (oracle : Query → Nat → SolverAdapter.Result → Prop) (bound : Int)
    (bad : SourceSymbolicIndex.Constraint Formula × Term (Label Formula)) (work : Nat)
    (run : PublicRun input oracle bound (.ok (.error bad)) work) :
    ∃ evaluationWork, Evaluates oracle bad evaluationWork .unknown := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, item, _, _, _, evaluationWork, _, _, caused⟩ :=
    public_first_stop input oracle bound (.unknown bad) work run
  obtain ⟨same, called⟩ := caused
  exact ⟨evaluationWork, same ▸ called⟩

/-- Completed successful IO traces satisfy the full independent public liquid contract. -/
theorem public_correct [DecidableEq State] [Ord (Label Formula)]
    (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (given : List Declaration) (integer : SourceReadLogicalIntegerAdapter.IntegerDeclarations given)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (bound : Int) (output : Table State (Term (Label Formula))) (work : Nat)
    (run : PublicRun input (SourceSizedLiquidAdapter.Call given milliseconds check) bound (.ok (.ok output)) work) :
    (∀ size term, term ∈ output input.root size ↔
      SourceSizedLiquidPublic.Accepts (FormulaLowering.sourceModel model) input.rows input.root term ∧
        RecursiveSize.nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, output input.root size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (sortedRows input) (truth (FormulaLowering.sourceModel model)))
        size input.root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through (output input.root) throughSize).Nodup ∧
      (SourceSizedQueries.through (output input.root) throughSize).Pairwise
        (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second)) ∧
    (∀ term size rank,
      SourceSizedQueries.rankSigned (output input.root) RecursiveSize.nodeSize term = some (size, rank) ↔
        SourceSizedQueries.unrankSigned (output input.root) size rank = some term) :=
  SourceSizedLiquidPublic.public_correct model allInteger given integer milliseconds check correct input bound output work
    (adapter_success input given milliseconds check bound output work run)

end MicroCFTA.SourceSizedLiquidExecutionPublic
