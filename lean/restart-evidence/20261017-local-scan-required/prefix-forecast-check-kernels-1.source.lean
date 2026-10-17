import MicroCFTA.SourceCurrentScanRequiredWorker
import MicroCFTA.SourceCurrentScanRequiredForecast
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace MicroCFTA.PrefixForecastCheck
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceEqualityClassOrder (Record)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "prepare" => SourceCurrentScanRequiredWorker.prepare
local notation "classes" => SourceCurrentAllocatedLocalWorker.classes
local notation "LocalOutcome" => SourceCurrentAllocatedLocalWorker.Outcome
local notation "Forecast" => SourceCurrentScanRequiredForecast
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance
private def before (width : Nat) : Checked width :=
  ⟨SourceRecursiveIntersectionThunks.initial width ⟨empty, Cache.emptyState⟩,
    SourceEqualityConstraintMemoAllocation.initial Cache.emptyState⟩
private def fourth := SourceCurrentEmptinessMemo.empty
private def memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard := SourceCurrentMemoMergeGraph.empty
private def record : Record := ⟨.branch [(0,.terminal), (1,.terminal)], [[0], [1]]⟩
private def deepRecord : Record := ⟨.branch [(0,.branch [(0,.terminal),(1,.terminal)])], [[0,0], [0,1]]⟩

/-- Zero primary fuel retains the exact failed source observation in both literal workers. -/
theorem primary_failure (width : Nat) :
    prepare 0 0 0 0 0 0 0 [record] [.reference .depth] (before width) fourth memo =
      .failed (.scan (.gate record.paths (.primary (.done none empty)))) (before width) fourth memo ∧
    classes 0 0 0 0 0 0 0 0 0 0 [record] [.reference .depth] (before width) fourth memo =
      .failed (.scan (.gate record.paths (.primary (.done none empty)))) (before width) fourth memo := by
  exact ⟨rfl, rfl⟩

/-- The selected empty child reaches Required, whose zero worker fuel retains its exact fault. -/
theorem required_failure (width : Nat) :
    prepare 1 0 0 0 0 0 0 [deepRecord] [.empty] (before width) fourth memo =
      .failed (.required (.exhausted .worker empty)) (before width) fourth memo ∧
    classes 1 0 0 0 0 0 0 0 0 0 [deepRecord] [.empty] (before width) fourth memo =
      .failed (.required (.exhausted .worker empty)) (before width) fourth memo := by
  exact ⟨rfl, rfl⟩

/-- Empty records preserve an unresolved prefix value, then the literal class pass propagates emptiness. -/
theorem empty_records_propagate (width : Nat) :
    prepare 0 0 0 0 0 0 0 [] [.reference .depth, .empty] (before width) fourth memo =
      .done (none, [], [.reference .depth, .empty]) (before width) fourth memo ∧
    classes 0 0 0 0 0 0 0 0 0 0 [] [.reference .depth, .empty] (before width) fourth memo =
      .done [.empty, .empty] (before width) fourth memo := by
  exact ⟨rfl, rfl⟩

/-- The two-occurrence initial schedule feeds Required only from its predicted Scan return. -/
theorem initial_stage_order (budget count : Nat) (alphabet : List Guard) (entry : Profile) :
    Forecast.scanProfile budget count [record, record] alphabet entry =
      (SourceCurrentScanNumericForecast.schedule budget count [record.paths, record.paths] alphabet entry).2 ∧
    Forecast.finalProfile budget count [record, record] alphabet entry =
      SourceCurrentInitialSelectionForecast.requiredProfile [record, record] count
        (Forecast.scanProfile budget count [record, record] alphabet entry) ∧
    Le entry (Forecast.scanProfile budget count [record, record] alphabet entry) ∧
    Le (Forecast.scanProfile budget count [record, record] alphabet entry)
      (Forecast.finalProfile budget count [record, record] alphabet entry) ∧
    SourceCurrentScanNumericForecast.fuel budget count [record.paths, record.paths] alphabet entry ≤
      Forecast.fuel budget count [record, record] alphabet entry ∧
    ∀ kept ∈ SourceCurrentInitialSelectionForecast.selections [record, record],
      Le (SourceCurrentConstrainedCapRequiredInitialNumeric.forecast
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count
        (Forecast.scanProfile budget count [record, record] alphabet entry))
        (Forecast.finalProfile budget count [record, record] alphabet entry) ∧
      SourceCurrentConstrainedCapRequiredInitialNumeric.workerFuel
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) ≤
        Forecast.fuel budget count [record, record] alphabet entry ∧
      SourceCurrentConstrainedCapRequiredInitialNumeric.readerFuel
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count
        (Forecast.scanProfile budget count [record, record] alphabet entry) ≤
        Forecast.fuel budget count [record, record] alphabet entry := by
  refine ⟨rfl, rfl, SourceCurrentScanNumericForecast.schedule_profile_ge _ _ _ _ _,
    Forecast.scan_le _ _ _ _ _, Forecast.scan_fuel _ _ _ _ _, ?_⟩
  intro kept included
  have selected := SourceCurrentInitialSelectionForecast.selection_sublist included
  exact ⟨SourceCurrentInitialSelectionForecast.required_selected selected count _,
    Forecast.required_worker selected budget count alphabet entry,
    Forecast.required_reader selected budget count alphabet entry⟩

end MicroCFTA.PrefixForecastCheck

#check @MicroCFTA.PrefixForecastCheck.primary_failure
#print axioms MicroCFTA.PrefixForecastCheck.primary_failure
#check @MicroCFTA.PrefixForecastCheck.required_failure
#print axioms MicroCFTA.PrefixForecastCheck.required_failure
#check @MicroCFTA.PrefixForecastCheck.empty_records_propagate
#print axioms MicroCFTA.PrefixForecastCheck.empty_records_propagate
#check @MicroCFTA.PrefixForecastCheck.initial_stage_order
#print axioms MicroCFTA.PrefixForecastCheck.initial_stage_order
