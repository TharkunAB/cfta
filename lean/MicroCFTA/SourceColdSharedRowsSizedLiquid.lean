import MicroCFTA.SourceColdSharedRowsSizedNative
import MicroCFTA.SourceSizedFiniteKeysNativeLiquid

/-!
# Solver-decided Sized execution on actual cold output rows

The independent ambient logical meaning is interpreted on the original
physical graph. Successful encoded source folds retain the canonical sequence,
finite class derivations, size order, bounded coverage, and both signed inverses.
Finite external attempts give finite outcomes, including Unknown and failures.
-/
namespace MicroCFTA.SourceColdSharedRows
open Language RecursiveSize SourceObservations SourceSymbolicIndex
open SolverAdapter SourceSizedLiquidProgram
open SourcePreparedSharedRows (encode)

variable {ModelValue : Type} [Ord (Label FullSyntax.Formula)]
  [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)]
  [DecidableEq (InternedConstructorTemplates.EdgeKey (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))]

/-- Actual encoded liquid execution on cold source rows has the original physical logical language. -/
theorem Trace.liquid_correct
    (state final : InternedConstructorTemplates.State (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))
    (value : InternedConstructorTemplates.Value (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))
    (rows : Rows (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))
    (trace : Trace state (fun _ => none) [value] rows final)
    (facts : InternedNestedFacts.Facts state) (prepared : MergedPhysicalWarmup.Prepared state)
    (available : InternedProbeProvenance.Available state value) (closed : value.free = [])
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (valid : FTAValidation.validateRows (encode value)
      (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)))
    (model : FormulaLowering.Model ModelValue) (given : List Declaration) (assumptions : List FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response)
    (bound : Int) (output : SourceSizedDecidedTable.Table SourceInternedRows.State (Term (Label FullSyntax.Formula))) (work : Nat)
    (run : SourceSizedFiniteKeysNativeLiquid.NativeRun (sizedTable (table rows keys value)) (encode value) valid
      (SourceSolverNamePublic.Call given assumptions milliseconds check) bound (.ok (.ok output)) work) :
    let meaning := SourceSizedLiquidAmbient.Meaning model given assumptions
    let holds := SourceSizedLiquidAmbientAdequacy.truth meaning
    let terms := output (encode value)
    (∀ size term, term ∈ terms size ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state holds) value term ∧ nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, terms size = if size ≤ bound.toNat then
      SourceSizedReference.classes (SourceSizedDecided.automaton
        (SourceSizedFiniteKeys.nativeSorted (sizedTable (table rows keys value)) (encode value) valid) holds) size (encode value) else []) ∧
    (∀ size, size ≤ bound.toNat → SourceSizedReference.ClassEvaluation
      (SourceSizedDecided.automaton (SourceSizedFiniteKeys.nativeSorted (sizedTable (table rows keys value)) (encode value) valid) holds)
      (size + 1) size (encode value) (terms size)) ∧
    (∀ throughSize, (SourceSizedQueries.through terms throughSize).Nodup ∧
      (SourceSizedQueries.through terms throughSize).Pairwise (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ throughSize term, term ∈ SourceSizedQueries.through terms throughSize ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state holds) value term ∧
        (nodeSize term : Int) ≤ bound ∧ nodeSize term ≤ throughSize) ∧
    (∀ term size rank, SourceSizedQueries.rankSigned terms nodeSize term = some (size, rank) ↔
      SourceSizedQueries.unrankSigned terms size rank = some term) ∧
    ((∀ request, ∃ attemptWork attempt, check request attemptWork attempt) →
      ∃ result actualWork, SourceSizedFiniteKeysNativeLiquid.NativeRun (sizedTable (table rows keys value)) (encode value) valid
        (SourceSolverNamePublic.Call given assumptions milliseconds check) bound result actualWork) := by
  dsimp only
  let meaning := SourceSizedLiquidAmbient.Meaning model given assumptions
  let holds := SourceSizedLiquidAmbientAdequacy.truth meaning
  obtain ⟨members, sequence, ordered, coverage, inverses⟩ := SourceSizedFiniteKeysNativeLiquid.encoded_correct
    (sizedTable (table rows keys value)) (encode value) valid model given assumptions milliseconds check correct bound output work run
  have language (term : Term (Label FullSyntax.Formula)) :
      SourceSizedLiquidAmbientPublic.Accepts meaning (SourceSizedFiniteKeys.lookup (sizedTable (table rows keys value))) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state holds) value term := by
    rw [← SourceSizedLiquidAmbientPublic.accepts_iff, sized_graph]
    exact trace.table_language state final value rows facts prepared available closed keys domain holds term
  refine ⟨?_, sequence, ?_, ordered, ?_, inverses, ?_⟩
  · intro size term
    rw [members, language]
  · intro size within
    rw [sequence, ite_eq_left within]
    exact SourceSizedReference.classes_evaluation_bound _ size _
  · intro throughSize term
    rw [coverage, language]
  · intro completed
    exact SourceSizedFiniteKeysNativeLiquid.encoded_finite (sizedTable (table rows keys value)) (encode value) valid
      given assumptions milliseconds check completed bound

end MicroCFTA.SourceColdSharedRows
