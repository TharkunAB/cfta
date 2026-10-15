import MicroCFTA.SourceSizedLiquidAppliedAmbient
import MicroCFTA.SourceSizedLiquidAmbientPublic
import MicroCFTA.SourceSolverNamePublic

/-!
# Current inferred-sort queries and the complete public Sized laws

Each external response concerns the current encoded request. Full source
query meaning follows from its actual inferred declaration domains. The
existing Sized proof then gives exact classes, order, and both inverses.
External answers, process execution, and elapsed time remain contracts.
-/
namespace MicroCFTA.SourceSolverAppliedPublic
open FullSyntax SolverAdapter SourceSizedLiquidProgram
open SourceSizedLiquidAppliedAmbient

/-- Each actual query uses the current complete encoded preparation. -/
inductive Call (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) : Query → Nat → Result → Prop where
  | preflight : SourceSolverAppliedPreparation.encodedPrepare given assumptions query = none →
      Call given assumptions milliseconds check query 1 (.returned .unknown)
  | checked : SourceSolverAppliedPreparation.encodedPrepare given assumptions query = some request →
      check request work attempt →
      Call given assumptions milliseconds check query (work + 1) (finish milliseconds attempt).result

/-- Correct actual encoded responses support the full current ambient query meaning. -/
theorem call_supports (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    {query work result} (called : Call given assumptions milliseconds check query work result) :
    ResultSupports result (Meaning model given assumptions query) := by
  cases called with
  | preflight _ => trivial
  | @checked request work attempt prepared checked =>
      cases attempt with
      | interrupted _ => trivial
      | answered response reached =>
          have responseCorrect := correct request work response reached checked
          have exactMeaning := encoded_unsat_iff_meaning model given assumptions query request prepared
          cases response with
          | unsat => exact exactMeaning.mp responseCorrect
          | sat => exact fun meaning => exactMeaning.mpr meaning responseCorrect
          | unknown => cases reached <;> trivial
          | error _ | unexpected _ => trivial

/-- Completing each actual external request supplies a finite call outcome. -/
theorem call_finite (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (query : Query) :
    ∃ work result, Call given assumptions milliseconds check query work result := by
  cases prepared : SourceSolverAppliedPreparation.encodedPrepare given assumptions query with
  | none => exact ⟨1, .returned .unknown, .preflight prepared⟩
  | some request =>
      obtain ⟨work, attempt, checked⟩ := completed request
      exact ⟨work + 1, _, .checked prepared checked⟩

/-- Application-free calls retain every historical result and occurrence-work count. -/
theorem app_free_call (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (query : Query) (work : Nat) (result : Result)
    (clear : SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent = []) :
    Call given assumptions milliseconds check query work result ↔
      SourceSolverNamePublic.Call given assumptions milliseconds check query work result := by
  constructor
  · intro called
    cases called with
    | preflight refused =>
        exact .preflight (by simpa only [SourceSolverAppliedPreparation.encoded_app_free given assumptions query clear] using refused)
    | checked prepared checked =>
        exact .checked (by simpa only [SourceSolverAppliedPreparation.encoded_app_free given assumptions query clear] using prepared) checked
  · intro called
    cases called with
    | preflight refused =>
        exact .preflight (by simpa only [SourceSolverAppliedPreparation.encoded_app_free given assumptions query clear] using refused)
    | checked prepared checked =>
        exact .checked (by simpa only [SourceSolverAppliedPreparation.encoded_app_free given assumptions query clear] using prepared) checked

open SourceObservations SourceSizedDecided SourceSizedDecidedTable SourceSizedDecidedPublic SourceSizedPreprocessing
open SourceSizedLiquidAmbientAdequacy

/-- Current per-call evidence derives the existing Sized guard adequacy contract. -/
theorem adapter_adequate (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response) :
    SourceSizedDecidedOperational.Adequate
      (SourceSizedLiquidAdequacy.Evaluates (Call given assumptions milliseconds check))
      (fun pair => truth (Meaning model given assumptions) pair.1 pair.2) :=
  sized_adequate _ _ (fun _ _ _ called => call_supports model given assumptions milliseconds check correct called)

/-- Successful public liquid generation is exact, canonical, distinct, size ordered, and invertible. -/
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
      SourceSizedLiquidAmbientPublic.Accepts (Meaning model given assumptions) input.rows input.root term ∧
        RecursiveSize.nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, output input.root size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (sortedRows input) (truth (Meaning model given assumptions)))
        size input.root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through (output input.root) throughSize).Nodup ∧
      (SourceSizedQueries.through (output input.root) throughSize).Pairwise
        (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second)) ∧
    (∀ term size rank,
      SourceSizedQueries.rankSigned (output input.root) RecursiveSize.nodeSize term = some (size, rank) ↔
        SourceSizedQueries.unrankSigned (output input.root) size rank = some term) := by
  let holds := truth (Meaning model given assumptions)
  let evaluator := SourceSizedLiquidAdequacy.Evaluates (Call given assumptions milliseconds check)
  have adequate := adapter_adequate model given assumptions milliseconds check correct
  have successful := SourceSizedLiquidExecutionPublic.public_success input _ bound output work run
  have pureRun := SourceSizedDecidedOperational.sizes_success (sortedRows input) (reached input)
    evaluator holds adequate successful output rfl
  let answer := SourceSizedDecidedOperational.ideal (Function.uncurry holds)
  have pureAdequate := SourceSizedDecidedOperational.ideal_adequate (Function.uncurry holds)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro size term
    rw [SourceSizedDecidedOperational.public_member_iff input evaluator holds adequate bound output work successful,
      SourceSizedLiquidAmbientPublic.accepts_iff]
  · exact fun size => SourceSizedDecidedOperational.public_reference_order input evaluator holds adequate
      bound output work successful size
  · intro throughSize
    exact ⟨SourceSizedDecidedQueries.enumeration_nodup (sortedRows input) (reached input) answer holds pureAdequate
      bound.toNat output pureRun input.root throughSize,
      SourceSizedDecidedQueries.size_ordered (sortedRows input) (reached input) answer holds pureAdequate
        bound.toNat output pureRun input.root throughSize⟩
  · intro term size rank
    exact ⟨SourceSizedDecidedQueries.unrankSigned_rankSigned (sortedRows input) (reached input) answer holds pureAdequate
      bound.toNat output pureRun input.root term size rank,
      SourceSizedDecidedQueries.rankSigned_unrankSigned (sortedRows input) (reached input) answer holds pureAdequate
        bound.toNat output pureRun input.root term size rank⟩

/-- External completion alone gives a finite bounded outcome, including Unknown and raised failures. -/
theorem public_finite [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (bound : Int) :
    ∃ result work, SourceSizedLiquidExecutionPublic.PublicRun input
      (Call given assumptions milliseconds check) bound result work :=
  SourceSizedLiquidExecutionPublic.public_finite input _
    (call_finite given assumptions milliseconds check completed) bound

end MicroCFTA.SourceSolverAppliedPublic
