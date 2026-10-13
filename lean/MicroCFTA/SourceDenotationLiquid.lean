import MicroCFTA.SourceDenotationEnumeration
import MicroCFTA.SourceSizedLiquidAmbientPublic

/-!
# Bounded liquid denotation from actual evaluator occurrences

The residual evaluator is the complete constraint program and repaired
ambient adapter. Returned decisions derive their meaning from each actual
external Sat or Unsat response. The source depth counts a leaf as zero.
This module covers the constrained branch after bounded constructor-row
exposure. The enumerator's finite protocol and storage contracts stay explicit.
-/

namespace MicroCFTA.SourceDenotationLiquid

open FullSyntax SourceObservations SourceSizedLiquidProgram SolverAdapter
open SourceSizedLiquidAmbientAdequacy EnumerationCorrectness EnumerationSemantics
open SourceSizedLiquidExecution

abbrev Symbol := Label Formula
abbrev Constraint := SourceSymbolicIndex.Constraint Formula
abbrev Tree := Language.Term Symbol
abbrev Item := Constraint × Tree

/-- Each residual occurrence executes the complete source evaluator, including equality checks. -/
abbrev Evaluation := SourceSizedLiquidExecutionPublic.Evaluation

/-- Actual complete evaluator traces derive the denotation callback law. -/
theorem evaluator_adequate (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response) :
    SourceDenotationEffects.Adequate
      (Evaluation (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check))
      (fun item => truth (SourceSizedLiquidAmbient.Meaning model given assumptions) item.1 item.2) := by
  intro item work verdict executed
  exact SourceSizedLiquidLogical.supports_congr verdict
    (truth_exact (SourceSizedLiquidAmbient.Meaning model given assumptions) item.1 item.2).symm
    (run_supports _ _ (fun _ _ _ called =>
      SourceSizedLiquidAmbientRepair.call_supports model given assumptions milliseconds check correct called)
      item.1 item.2 executed)

/-- A leaf has source depth zero; the checked language height is one greater. -/
theorem depth_bound (term : Tree) (bound : Int) (nonnegative : 0 ≤ bound) :
    term.height ≤ bound.toNat + 1 ↔ ((term.height - 1 : Nat) : Int) ≤ bound := by
  have positive := term.height_pos
  omega

/-- A signed constrained denotation query keeps Unknown inside the returned result and exceptions outside it. -/
def Run (oracle : Query → Nat → Result → Prop) (source : Nat → List (EnumerationState.Edge Symbol Constraint))
    (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat) (meet : Nat → Nat → Nat)
    (bound : Int) (fuel node : Nat) (result : Outcome Item (List Tree)) (work : Nat) : Prop :=
  if bound < 0 then result = .ok (.ok []) ∧ work = 0 else
    SourceDenotationRuns.Run (Evaluation oracle)
      (SourceDenotationEnumeration.rows
        (EnumerationBoundedRows.graph encode decode source (EnumerationBoundedRows.boundedMeet encode decode meet))
        ("Mu", .top) fuel (encode (bound.toNat + 1, node))) (SourceSizedLiquidExecution.encode result) work

/-- Negative depth returns an empty list without invoking enumeration or the solver. -/
theorem negative (oracle : Query → Nat → Result → Prop) (source : Nat → List (EnumerationState.Edge Symbol Constraint))
    (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat) (meet : Nat → Nat → Nat)
    (bound : Int) (below : bound < 0) (fuel node : Nat) :
    Run oracle source encode decode meet bound fuel node (.ok (.ok [])) 0 := by simp [Run, below]

/-- Every finite protocol list gives a finite denotation outcome from completed external attempts. -/
theorem finite (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt)
    (source : Nat → List (EnumerationState.Edge Symbol Constraint))
    (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat) (meet : Nat → Nat → Nat)
    (bound : Int) (fuel node : Nat) :
    ∃ result work, Run (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check)
      source encode decode meet bound fuel node result work := by
  by_cases below : bound < 0
  · exact ⟨.ok (.ok []), 0, negative _ source encode decode meet bound below fuel node⟩
  · obtain ⟨result, work, run⟩ := SourceDenotationRuns.finite
      (Evaluation (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check))
      (fun item => SourceSizedLiquidProgram.finite_execution _
        (SourceSizedLiquidAmbientRepair.call_finite given assumptions milliseconds check completed)
        (SourceSizedLiquidEvaluation.constraintProgram item.1 item.2))
      (SourceDenotationEnumeration.rows
        (EnumerationBoundedRows.graph encode decode source (EnumerationBoundedRows.boundedMeet encode decode meet))
        ("Mu", .top) fuel (encode (bound.toNat + 1, node)))
    exact ⟨SourceSizedLiquidExecution.decode result, work,
      by simpa only [Run, below, ↓reduceIte, encode_decode] using run⟩

/-- One sufficient protocol bound gives the exact original accepted language below the signed source depth. -/
theorem eventual_exact (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat) (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge Symbol Constraint)) (meet : Nat → Nat → Nat)
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (sourceRows : EnumerationIntersection.HashRows (fun state => (source state).map
      (EnumerationLanguage.edgeView (Logical (SourceSizedLiquidAmbient.Meaning model given assumptions)))) meet)
    (bound : Int) (nonnegative : 0 ≤ bound) (node : Nat) :
    ∃ cutoff, ∀ fuel, cutoff ≤ fuel → ∀ output work,
      Run (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check)
        source encode decode meet bound fuel node (.ok (.ok output)) work →
      output.Nodup ∧ ∀ term, term ∈ output ↔
        Language.Accepts (fun state => (source state).map
          (EnumerationLanguage.edgeView (Logical (SourceSizedLiquidAmbient.Meaning model given assumptions)))) node term ∧
          ((term.height - 1 : Nat) : Int) ≤ bound := by
  let meaning := Logical (SourceSizedLiquidAmbient.Meaning model given assumptions)
  let graph := EnumerationBoundedRows.graph encode decode source (EnumerationBoundedRows.boundedMeet encode decode meet)
  obtain ⟨cutoff, sufficient⟩ := SourceDenotationEnumeration.bounded_sufficient encode decode roundtrip source meet valid
    meaning sourceRows ("Mu", .top) (bound.toNat + 1) node
  refine ⟨cutoff, ?_⟩
  intro fuel enough output work run
  have actual : SourceDenotationRuns.Run
      (Evaluation (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check))
      (SourceDenotationEnumeration.rows graph ("Mu", .top) fuel (encode (bound.toNat + 1, node))) (.ok output) work := by
    simpa only [Run, show ¬bound < 0 by omega, ↓reduceIte, SourceSizedLiquidExecution.encode] using run
  refine ⟨SourceDenotationRuns.nodup _ _ output work actual, ?_⟩
  intro term
  rw [SourceDenotationEnumeration.successful_exact graph meaning
    (EnumerationBoundedRows.complete encode decode source _ valid)
    (EnumerationBoundedRows.intersection_correct encode decode roundtrip source meet valid meaning sourceRows)
    ("Mu", .top) fuel (encode (bound.toNat + 1, node)) (sufficient fuel enough)
    (fun item => truth (SourceSizedLiquidAmbient.Meaning model given assumptions) item.1 item.2)
    (fun item => truth_exact _ item.1 item.2) _
    (evaluator_adequate model given assumptions milliseconds check correct) output work actual term]
  exact (EnumerationBoundedRows.accepted_exact encode decode roundtrip source _ valid meaning
    (bound.toNat + 1) node term).trans (and_congr Iff.rfl (depth_bound term bound nonnegative))

/-- A denotation exception originates in the exact external query occurrence that raised it. -/
theorem exception_origin (oracle : Query → Nat → Result → Prop) (rows : List (Tree × List Item))
    (failure : Failure) (work : Nat)
    (run : SourceDenotationRuns.Run (Evaluation oracle) rows (.error (.raised failure)) work) :
    ∃ query queryWork, oracle query queryWork (.raised failure) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, caused⟩ :=
    SourceDenotationRuns.first_stop (Evaluation oracle) rows (.raised failure) work run
  exact SourceSizedLiquidProgram.raised_origin oracle caused failure rfl

end MicroCFTA.SourceDenotationLiquid
