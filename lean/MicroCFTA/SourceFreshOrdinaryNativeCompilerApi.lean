import MicroCFTA.SourceFreshOrdinaryNativeCompiler
import MicroCFTA.SourceSizedDispatcher
import MicroCFTA.SourceCyclicRowsExecution

/-!
# Complete Sized query records after actual native compilation

The derived native compiler result supplies plain distinct rows. All four
optimized queries equal the reference query record, including signed inputs.
One finite minimum prepass supports every node-count class.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeCompiler
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows Supported ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)

section Input
variable {width : Nat} {Formula Key : Type} [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (source : InternedConstructorTemplates.State (Label Formula) (Constraint Formula))
    (rows : Rows (Label Formula) (Constraint Formula)) (keys : List Nat)
    (value : Value (Label Formula) (Constraint Formula))
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (supported : Supported rows value)
    (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys value))
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows keys value) state →
      SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)

local notation "raw" => SourceColdSharedRows.table rows keys value
local notation "input" => SourceFreshOrdinaryColdCyclic.input rows keys value domain supported closed freeVariables active
local notation "K" => SourceDenseRows.Member (SourceDenseRows.keys raw)
local notation "N" => SourceRecursiveIntersectionThunks.State width (Label Formula) (Constraint Formula)
local notation "invariant" => SourceFreshOrdinaryNativeKeyScan.Invariant emptyGuard conjoin source

local notation "execution" => Execution emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
local notation "rangeCheck" => Ranges emptyGuard conjoin source rows keys value domain supported closed freeVariables active order

variable (semantic : SemanticHeap source) (covered : Covered [] source)
    (guarded : InternedGuardedProbeHeap.Heap source) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source)
    (replayed : ReplayedRows source rows) (resident : ResidentRows source rows) (closedRows : CoveredRows rows rows)

include semantic covered guarded budgetHeap replayed resident closedRows

/-- Every successful actual native compiler gives the identical complete optimized and reference query record. -/
theorem api_record (state : N) (valid : invariant state) (ranges : rangeCheck state)
    (output : Automaton K (Label Formula)) (after : N) (actual : execution state (.ok output) after) :
    SourceSizedDispatcher.optimizedApi output (input).root = SourceSizedDispatcher.referenceApi output (input).root := by
  have success := (execution_correct emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
    semantic covered guarded budgetHeap replayed resident closedRows state valid ranges (.ok output) after actual).2
  obtain ⟨plain, unique, _⟩ := SourceCyclicRows.compile_exact formulas solver input order output success
  have reference := SourceSizedReference.classes_eq_enumerate output plain unique
  change SourceSizedDispatcher.Api.mk _ _ _ _ = SourceSizedDispatcher.Api.mk _ _ _ _
  congr 1
  · funext size
    rw [SourceSizedDispatch.terms_exact, SourceSizedDispatcher.reference_terms_toNat, reference]
  · funext size
    dsimp only [SourceSizedDispatcher.optimizedApi, SourceSizedDispatcher.referenceApi, SourceSizedQueries.countSigned]
    rw [RecursiveSize.countAt_correct, SourceSizedDispatcher.reference_terms_toNat, reference]
  · funext size rank
    dsimp only [SourceSizedDispatcher.optimizedApi, SourceSizedDispatcher.referenceApi, SourceSizedQueries.unrankSigned]
    rw [SourceSizedDispatch.select_exact, SourceSizedDispatcher.reference_terms_toNat, reference]
    by_cases negative : rank < 0
    · simp [negative, show ¬0 ≤ rank by omega]
    · simp [negative, show 0 ≤ rank by omega]
  · funext term
    rw [TablePosition.positionsOf_eq_termPosition output plain unique, SizedRank.termPosition]
    simp only [SourceSizedQueries.rank, reference]
    rfl

/-- One finite minimum prepass supports every exact-size class query of an actual native compiler result. -/
theorem finite_prepass (state : N) (valid : invariant state) (ranges : rangeCheck state)
    (output : Automaton K (Label Formula)) (after : N) (actual : execution state (.ok output) after) :
    ∃ fuel, MinimumSize.sweeps output (List.attach (SourceDenseRows.keys raw)) fuel (fun _ => none) =
        SourceRowsMinimum.minimumSizes output (List.attach (SourceDenseRows.keys raw)) ∧
      MinimumSize.sweep output (List.attach (SourceDenseRows.keys raw))
          (SourceRowsMinimum.minimumSizes output (List.attach (SourceDenseRows.keys raw))) =
        SourceRowsMinimum.minimumSizes output (List.attach (SourceDenseRows.keys raw)) ∧
      ∀ size, SourceSizedTableEvaluation.Evaluation output (size + 1) size (input).root
        (RecursiveSize.countAt output size (input).root) (RecursiveSize.compileAt output size (input).root) := by
  have success := (execution_correct emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
    semantic covered guarded budgetHeap replayed resident closedRows state valid ranges (.ok output) after actual).2
  obtain ⟨fuel, reached, stable⟩ := (SourceCyclicRowsExecution.minimum_prepass formulas solver input order output success).1
  exact ⟨fuel, reached, stable, fun size => SourceSizedTableEvaluation.finite_bound output size (input).root⟩

end Input
end MicroCFTA.SourceFreshOrdinaryNativeCompiler
