import MicroCFTA.SourceSolverNamePreparation
import MicroCFTA.SourceSizedLiquidAmbientPublic

/-!
# Encoded solver requests and the public liquid language theorem

The actual encoded preflight preserves all call outcomes and occurrence
work. Correct external answers concern the encoded requests. Injectivity
and quantified semantics derive the original query response contract.
The complete bounded language, order, and rank laws therefore apply to
the repaired source without assuming unencoded external answers.
-/
namespace MicroCFTA.SourceSolverNamePublic
open FullSyntax SolverAdapter SourceSizedLiquidProgram
open SourceSolverNameSemantics SourceSolverNameFastEncoding SourceSolverNamePreparation

/-- Interpret one actual external check at the encoded source request. -/
def translated (check : Prepared → Nat → Attempt → Prop) (request : Prepared) : Nat → Attempt → Prop :=
  check (renamePrepared encode request)

/-- The actual adapter calls the solver only after encoded preflight succeeds. -/
inductive Call (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) : Query → Nat → Result → Prop where
  | preflight : encodedPrepare given assumptions query = none →
      Call given assumptions milliseconds check query 1 (.returned .unknown)
  | checked : encodedPrepare given assumptions query = some request → check request work attempt →
      Call given assumptions milliseconds check query (work + 1) (finish milliseconds attempt).result

/-- The encoded and original call relations agree for each outcome and finite work. -/
theorem call_iff (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (query : Query) (work : Nat) (result : Result) :
    Call given assumptions milliseconds check query work result ↔
      SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds (translated check) query work result := by
  constructor
  · intro called
    cases called with
    | preflight rejected =>
      rw [sourcePrepare_encode] at rejected
      exact .preflight (Option.map_eq_none_iff.mp rejected)
    | @checked request work attempt prepared called =>
      rw [sourcePrepare_encode] at prepared
      cases original : SourceSizedLiquidAmbientRepair.prepareQuery given assumptions query with
      | none => simp [original] at prepared
      | some unencoded =>
        simp only [original, Option.map_some, Option.some.injEq] at prepared
        subst request
        exact .checked original called
  · intro called
    cases called with
    | preflight rejected =>
      exact .preflight (by rw [sourcePrepare_encode, rejected]; rfl)
    | checked prepared called =>
      exact .checked (by rw [sourcePrepare_encode, prepared]; rfl) called

/-- Exact call equality transfers complete public traces, including raised errors. -/
theorem call_eq (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) :
    Call given assumptions milliseconds check =
      SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds (translated check) := by
  funext query work result
  exact propext (call_iff given assumptions milliseconds check query work result)

/-- Both Sat and Unsat retain their original meaning after concrete encoding. -/
theorem response_correct (model : FormulaLowering.Model Value) (request : Prepared) (response : Response) :
    ResponseCorrect model (renamePrepared encode request) response ↔ ResponseCorrect model request response := by
  cases response <;> simp only [ResponseCorrect, satisfiable_rename model encode (fun _ _ same => encode_injective same)]

/-- Correct actual encoded responses supply the former mathematical request contract. -/
theorem translated_correct (model : FormulaLowering.Model Value)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response) :
    ∀ request work response reached, translated check request work (.answered response reached) →
      ResponseCorrect model request response := by
  intro request work response reached called
  exact (response_correct model request response).mp (correct _ work response reached called)

/-- Each actual encoded call supports the independent mixed-sort ambient meaning. -/
theorem call_supports (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    {query work result} (called : Call given assumptions milliseconds check query work result) :
    ResultSupports result (SourceSizedLiquidAmbient.Meaning model given assumptions query) :=
  SourceSizedLiquidAmbientRepair.call_supports model given assumptions milliseconds (translated check)
    (translated_correct model check correct)
    ((call_iff given assumptions milliseconds check query work result).mp called)

/-- Finite encoded attempts give finite outcomes without a stable-reply assumption. -/
theorem call_finite (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (query : Query) :
    ∃ work result, Call given assumptions milliseconds check query work result := by
  rw [call_eq]
  exact SourceSizedLiquidAmbientRepair.call_finite given assumptions milliseconds (translated check)
    (fun request => completed (renamePrepared encode request)) query

open SourceObservations SourceSizedDecided SourceSizedDecidedTable SourceSizedDecidedPublic SourceSizedPreprocessing
open SourceSizedLiquidAmbientAdequacy

/-- Encoded source queries derive the complete exact-size, ordered, distinct, invertible liquid result. -/
theorem public_correct [DecidableEq State] [Ord (Label Formula)]
    (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (bound : Int) (output : Table State (Language.Term (Label Formula))) (work : Nat)
    (run : SourceSizedLiquidExecutionPublic.PublicRun input
      (Call given assumptions milliseconds check) bound (.ok (.ok output)) work) :
    (∀ size term, term ∈ output input.root size ↔
      SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAmbient.Meaning model given assumptions)
        input.rows input.root term ∧ RecursiveSize.nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, output input.root size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (sortedRows input) (truth (SourceSizedLiquidAmbient.Meaning model given assumptions)))
        size input.root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through (output input.root) throughSize).Nodup ∧
      (SourceSizedQueries.through (output input.root) throughSize).Pairwise
        (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second)) ∧
    (∀ term size rank,
      SourceSizedQueries.rankSigned (output input.root) RecursiveSize.nodeSize term = some (size, rank) ↔
        SourceSizedQueries.unrankSigned (output input.root) size rank = some term) := by
  rw [call_eq] at run
  exact SourceSizedLiquidAmbientPublic.public_correct model given assumptions milliseconds (translated check)
    (translated_correct model check correct) input bound output work run

/-- Every bounded public run has a finite outcome if its encoded external requests finish. -/
theorem public_finite [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (bound : Int) :
    ∃ result work, SourceSizedLiquidExecutionPublic.PublicRun input
      (Call given assumptions milliseconds check) bound result work :=
  SourceSizedLiquidExecutionPublic.public_finite input _
    (call_finite given assumptions milliseconds check completed) bound

end MicroCFTA.SourceSolverNamePublic
