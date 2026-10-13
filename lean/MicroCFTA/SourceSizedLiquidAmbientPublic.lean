import MicroCFTA.SourceSizedLiquidAmbientAdequacy
import MicroCFTA.SourceSizedLiquidExecutionPublic

/-!
# Exact bounded liquid generation in a mixed-sort ambient context

The repaired public adapter preserves ambient assumptions and inherited
sorts. Successful whole-IO traces have the independent accepted language,
canonical sequence, size order, and both rank inverse laws. Completion can
produce GuardUnknown or a raised external failure without stable replies.
-/

namespace MicroCFTA.SourceSizedLiquidAmbientPublic

open FullSyntax SourceObservations SourceSizedDecided SourceSizedDecidedTable
open SourceSizedDecidedExecution SourceSizedDecidedPublic SourceSizedPreprocessing
open SourceSizedLiquidAmbientAdequacy SourceSizedLiquidProgram SolverAdapter

/-- An accepted finite tree has one original transition and logically valid complete children and constraint. -/
inductive Accepts (meaning : Query → Prop)
    (rows : State → List (Row State (Label Formula) (SourceSymbolicIndex.Constraint Formula))) :
    State → Language.Term (Label Formula) → Prop where
  | node (row : Row State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
      (children : List (Language.Term (Label Formula))) :
      row ∈ rows state → Language.All₂ (Accepts meaning rows) row.children children →
      Logical meaning row.constraint (.node row.label children) →
      Accepts meaning rows state (.node row.label children)

/-- The independent liquid derivation is exactly the mathematical graph language. -/
theorem accepts_iff (meaning : Query → Prop)
    (rows : State → List (Row State (Label Formula) (SourceSymbolicIndex.Constraint Formula)))
    (state : State) (term : Language.Term (Label Formula)) :
    Language.Accepts (automaton rows (truth meaning)) state term ↔ Accepts meaning rows state term := by
  constructor
  · intro accepted
    induction accepted using Language.Accepts.rec
      (motive_2 := fun states terms _ => Language.All₂ (Accepts meaning rows) states terms) with
    | node edge children member runs guard ih =>
        obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
        subst edge
        exact .node row children rowMember ih ((truth_exact meaning row.constraint _).mp guard)
    | nil => exact .nil
    | cons head tail ihHead ihTail => exact .cons ihHead ihTail
  · intro accepted
    induction accepted using Accepts.rec
      (motive_2 := fun states terms _ => Language.All₂ (Language.Accepts (automaton rows (truth meaning))) states terms) with
    | node row children member runs guard ih =>
        exact .node (row.edge (truth meaning)) children (List.mem_map.mpr ⟨row, member, rfl⟩) ih
          ((truth_exact meaning row.constraint _).mpr guard)
    | nil => exact .nil
    | cons head tail ihHead ihTail => exact .cons ihHead ihTail

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
      (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check) bound (.ok (.ok output)) work) :
    (∀ size term, term ∈ output input.root size ↔
      Accepts (SourceSizedLiquidAmbient.Meaning model given assumptions) input.rows input.root term ∧
        RecursiveSize.nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, output input.root size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (sortedRows input) (truth (SourceSizedLiquidAmbient.Meaning model given assumptions)))
        size input.root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through (output input.root) throughSize).Nodup ∧
      (SourceSizedQueries.through (output input.root) throughSize).Pairwise
        (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second)) ∧
    (∀ term size rank,
      SourceSizedQueries.rankSigned (output input.root) RecursiveSize.nodeSize term = some (size, rank) ↔
        SourceSizedQueries.unrankSigned (output input.root) size rank = some term) := by
  let holds := truth (SourceSizedLiquidAmbient.Meaning model given assumptions)
  let evaluator := SourceSizedLiquidAdequacy.Evaluates (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check)
  have adequate := adapter_adequate model given assumptions milliseconds check correct
  have successful := SourceSizedLiquidExecutionPublic.public_success input _ bound output work run
  have pureRun := SourceSizedDecidedOperational.sizes_success (sortedRows input) (reached input)
    evaluator holds adequate successful output rfl
  let answer := SourceSizedDecidedOperational.ideal (Function.uncurry holds)
  have pureAdequate := SourceSizedDecidedOperational.ideal_adequate (Function.uncurry holds)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro size term
    rw [SourceSizedDecidedOperational.public_member_iff input evaluator holds adequate bound output work successful,
      accepts_iff]
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
      (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check) bound result work :=
  SourceSizedLiquidExecutionPublic.public_finite input _
    (SourceSizedLiquidAmbientRepair.call_finite given assumptions milliseconds check completed) bound

end MicroCFTA.SourceSizedLiquidAmbientPublic
