import MicroCFTA.SourceCurrentScanRequiredWorker
import MicroCFTA.SourceCurrentScanRequiredForecast
set_option linter.all true
set_option pp.explicit false
set_option pp.fullNames false
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

example (width : Nat) :
    prepare 0 0 0 0 0 0 0 [] [.reference .depth, .empty] (before width) fourth memo =
      .done (none, [], [.reference .depth, .empty]) (before width) fourth memo := by
  dsimp [SourceCurrentScanRequiredWorker.prepare, SourceCurrentAllocatedLocalWorker.scan,
    SourceCurrentAllocatedRecordScanWorker.scan, SourceCurrentAllocatedLocalWorker.required,
    SourceEqualityRequiredExecution.requireAll, SourceEqualitySelectedRequired.paths,
    EqualityNormalize.canonicalClass, SourceEqualityNeeded.build,
    SourceEqualityRequiredWorker.children, SourceEqualityNeededMap.lookup,
    SourceCurrentAllocatedLocalWorker.Outcome.bind, SourceEqualityRequiredWorker.Result.bind,
    SourceCurrentConjunctionClassScan.advanceHeap, before,
    SourceCurrentAllocatedNativeEffects.physical]
  trace_state

end MicroCFTA.PrefixForecastCheck
