import MicroCFTA.SourceSizedLiquidAdequacy

/-!
# Bounded exact generation for independently interpreted liquid automata

Acceptance below is a finite raw-row derivation with mathematical guard
satisfaction. It contains no evaluator verdict. The public theorem derives
the evaluator contract from each actual external Sat or Unsat response.
The adapter domain is all-Int with no ambient assumptions. Replies can vary
between repeated queries. Unknown fails the size query; exceptions remain
outside the returned size-table result.
-/

namespace MicroCFTA.SourceSizedLiquidPublic

open FullSyntax SourceObservations SourceSizedDecided SourceSizedDecidedTable
open SourceSizedDecidedExecution SourceSizedDecidedPublic SourceSizedPreprocessing
open SourceSizedLiquidAdequacy SourceSizedLiquidProgram SolverAdapter

/-- An accepted finite tree has one original transition and logically valid complete children and constraint. -/
inductive Accepts (model : Interpretation Value)
    (rows : State → List (Row State (Label Formula) (SourceSymbolicIndex.Constraint Formula))) :
    State → Language.Term (Label Formula) → Prop where
  | node (row : Row State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
      (children : List (Language.Term (Label Formula))) :
      row ∈ rows state → Language.All₂ (Accepts model rows) row.children children →
      Logical model row.constraint (.node row.label children) →
      Accepts model rows state (.node row.label children)

/-- The independent liquid derivation is exactly the mathematical graph language. -/
theorem accepts_iff (model : Interpretation Value)
    (rows : State → List (Row State (Label Formula) (SourceSymbolicIndex.Constraint Formula)))
    (state : State) (term : Language.Term (Label Formula)) :
    Language.Accepts (automaton rows (truth model)) state term ↔ Accepts model rows state term := by
  constructor
  · intro accepted
    induction accepted using Language.Accepts.rec
      (motive_2 := fun states terms _ => Language.All₂ (Accepts model rows) states terms) with
    | node edge children member runs guard ih =>
        obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
        subst edge
        exact .node row children rowMember ih ((truth_exact model row.constraint _).mp guard)
    | nil => exact .nil
    | cons head tail ihHead ihTail => exact .cons ihHead ihTail
  · intro accepted
    induction accepted using Accepts.rec
      (motive_2 := fun states terms _ => Language.All₂ (Language.Accepts (automaton rows (truth model))) states terms) with
    | node row children member runs guard ih =>
        exact .node (row.edge (truth model)) children (List.mem_map.mpr ⟨row, member, rfl⟩) ih
          ((truth_exact model row.constraint _).mpr guard)
    | nil => exact .nil
    | cons head tail ihHead ihTail => exact .cons ihHead ihTail

/-- A public run uses actual sorted rows, original trim keys, and complete adapter query occurrences. -/
abbrev SizedRun [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (given : List Declaration) (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (bound : Int) (result : Except (SourceSymbolicIndex.Constraint Formula × Language.Term (Label Formula))
      (Table State (Language.Term (Label Formula)))) (work : Nat) : Prop :=
  SizesRun (ClassRun (sortedRows input) (Evaluates (SourceSizedLiquidAdapter.Call given milliseconds check)))
    (reached input) bound.toNat result work

/-- Successful public liquid generation is exact, canonical, distinct, size ordered, and invertible. -/
theorem public_correct [DecidableEq State] [Ord (Label Formula)]
    (model : FormulaLowering.Model Value) (allInteger : ∀ value, model.hasSort .int value)
    (given : List Declaration) (integer : SourceReadLogicalIntegerAdapter.IntegerDeclarations given)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (bound : Int) (output : Table State (Language.Term (Label Formula))) (work : Nat)
    (run : SizedRun input given milliseconds check bound (.ok output) work) :
    (∀ size term, term ∈ output input.root size ↔
      Accepts (FormulaLowering.sourceModel model) input.rows input.root term ∧
        RecursiveSize.nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, output input.root size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (sortedRows input) (truth (FormulaLowering.sourceModel model)))
        size input.root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through (output input.root) throughSize).Nodup ∧
      (SourceSizedQueries.through (output input.root) throughSize).Pairwise
        (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second)) ∧
    (∀ term size rank,
      SourceSizedQueries.rankSigned (output input.root) RecursiveSize.nodeSize term = some (size, rank) ↔
        SourceSizedQueries.unrankSigned (output input.root) size rank = some term) := by
  let holds := truth (FormulaLowering.sourceModel model)
  let evaluator := Evaluates (SourceSizedLiquidAdapter.Call given milliseconds check)
  have adequate := adapter_adequate model allInteger given integer milliseconds check correct
  have pureRun := SourceSizedDecidedOperational.sizes_success (sortedRows input) (reached input)
    evaluator holds adequate run output rfl
  let answer := SourceSizedDecidedOperational.ideal (Function.uncurry holds)
  have pureAdequate := SourceSizedDecidedOperational.ideal_adequate (Function.uncurry holds)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro size term
    rw [SourceSizedDecidedOperational.public_member_iff input evaluator holds adequate bound output work run,
      accepts_iff]
  · exact fun size => SourceSizedDecidedOperational.public_reference_order input evaluator holds adequate
      bound output work run size
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

/-- Finite returned query witnesses give a finite public result, including GuardUnknown. -/
theorem public_finite [DecidableEq State] [Ord (Label Formula)]
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (given : List Declaration) (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (returned : ∀ query, ∃ work verdict, SourceSizedLiquidAdapter.Call given milliseconds check query work (.returned verdict))
    (bound : Int) : ∃ result work, SizedRun input given milliseconds check bound result work :=
  SourceSizedDecidedOperational.public_finite input _
    (sized_terminates (SourceSizedLiquidAdapter.Call given milliseconds check) returned) bound

/-- External checks that merely finish can also yield a raised exception; this is not a GuardUnknown result. -/
theorem constraint_outcome (given : List Declaration) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) :
    ∃ work result, Run (SourceSizedLiquidAdapter.Call given milliseconds check)
      (SourceSizedLiquidEvaluation.constraintProgram constraint term) result work :=
  finite_execution _ (SourceSizedLiquidAdapter.call_finite given milliseconds check completed) _

/-- A raised constraint failure is the unchanged failure of an actual adapter query. -/
theorem constraint_exception (given : List Declaration) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula))
    (err : Failure) (work : Nat)
    (run : Run (SourceSizedLiquidAdapter.Call given milliseconds check)
      (SourceSizedLiquidEvaluation.constraintProgram constraint term) (.raised err) work) :
    ∃ query queryWork, SourceSizedLiquidAdapter.Call given milliseconds check query queryWork (.raised err) :=
  raised_origin _ run err rfl

end MicroCFTA.SourceSizedLiquidPublic
