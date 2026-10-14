import MicroCFTA.SourceFreshOrdinaryColdValidated
import MicroCFTA.SourceFreshOrdinaryColdGuardedExact
import MicroCFTA.SourceSizedFiniteKeysLiquidApiLaws

/-!
# Exact solver-decided queries after general repaired cold traversal

The actual public FTA builder validates normalized raw rows. Its successful
result supplies the finite query input. The independent guarded language
of the original physical root determines every bounded query law.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache Language RecursiveSize InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceObservations SourceSymbolicIndex SourceSizedFiniteKeys
open SolverAdapter SourceSizedLiquidProgram
open SourcePreparedSharedRows (encode)
open SourceColdSharedRows (Rows sizedTable table)

variable {ModelValue : Type} [Ord (Label FullSyntax.Formula)]
    [Std.TransOrd (Label FullSyntax.Formula)] [Std.LawfulEqOrd (Label FullSyntax.Formula)]
    [DecidableEq (EdgeKey (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))]
    (state final : State (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))
    (value : Value (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))
    (rows : Rows (Label FullSyntax.Formula) (Constraint FullSyntax.Formula))
    (trace : Trace state (fun _ => none) [value] rows final)
    (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (available : Available state value) (closed : value.free = []) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)

local notation "raw" => sizedTable (table rows keys value)
local notation "normalizedRaw" => normalized raw

include trace semantic covered guarded budgetHeap available closed domain

omit [Ord (Label FullSyntax.Formula)] [Std.TransOrd (Label FullSyntax.Formula)]
  [Std.LawfulEqOrd (Label FullSyntax.Formula)] in
/-- Actual validated normalized cold rows retain the independent original physical language. -/
theorem Trace.liquid_language (model : FormulaLowering.Model ModelValue) (given : List Declaration)
    (assumptions : List FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env (Label FullSyntax.Formula))
    (term : Term (Label FullSyntax.Formula)) :
    SourceSizedLiquidAmbientPublic.Accepts (SourceSizedLiquidAmbient.Meaning model given assumptions)
      (lookup normalizedRaw) (encode value) term ↔
      InternedGuardedLanguage.meaning (SourceSizedLiquidAmbientAdequacy.truth
        (SourceSizedLiquidAmbient.Meaning model given assumptions)) ambient value term := by
  rw [← SourceSizedLiquidAmbientPublic.accepts_iff, normalized_graph, SourceColdSharedRows.sized_graph]
  exact SourceFreshOrdinaryColdGuardedExact.trace_table_exact state final value rows trace semantic covered
    guarded budgetHeap available closed keys domain _ ambient term

/-- Every successful actual encoded fold over the validated cold output has all exact bounded query laws. -/
theorem Trace.liquid_exact
    (success : FTAValidation.mkFTA (encode value) (interpreted raw (fun _ _ => true)) =
      .ok (interpreted normalizedRaw (fun _ _ => true)))
    (model : FormulaLowering.Model ModelValue) (given : List Declaration) (assumptions : List FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response)
    (bound : Int) (output : SourceSizedDecidedTable.Table SourceInternedRows.State (Term (Label FullSyntax.Formula)))
    (work : Nat)
    (run : SourceSizedFiniteKeysNativeLiquid.NativeRun normalizedRaw (encode value)
      (normalized_validated raw (encode value) success) (SourceSolverNamePublic.Call given assumptions milliseconds check)
      bound (.ok (.ok output)) work) (ambient : InternedGuardedLanguage.Env (Label FullSyntax.Formula)) :
    SourceSizedApiLaws.Exact (SourceSizedBoundedApiLaws.fromClasses (output (encode value)))
      (fun term => InternedGuardedLanguage.meaning (SourceSizedLiquidAmbientAdequacy.truth
        (SourceSizedLiquidAmbient.Meaning model given assumptions)) ambient value term ∧ (nodeSize term : Int) ≤ bound) := by
  have exactQueries := SourceSizedFiniteKeysNativeLiquid.encoded_exact normalizedRaw (encode value)
    (normalized_validated raw (encode value) success) model given assumptions milliseconds check correct bound output work run
  have language := trace.liquid_language state final value rows semantic covered guarded budgetHeap available closed keys domain
    model given assumptions ambient
  simpa only [language] using exactQueries

end MicroCFTA.SourceFreshOrdinaryColdSharedRows
