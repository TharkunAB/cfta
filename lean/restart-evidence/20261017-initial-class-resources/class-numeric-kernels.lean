import MicroCFTA.SourceCurrentConstrainedCapClassNumeric
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.ClassNumericInitialKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "classProfile" => SourceCurrentConstrainedCapClassForecast.classProfile
local notation "classFuel" => SourceCurrentConstrainedCapClassForecast.classFuel
local notation "classDepth" => SourceCurrentConstrainedCapMixedClass.classDepth
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Own initial completion yields exact class language and all larger full-state worker returns. -/
theorem initial_contract (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (merged : MergeStored memo) (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (bounded : ∀ value ∈ values, Cap Plain depth value)
    (room : Room bits (classProfile record values.length profile)) :
    ∃ results after saved next,
      Frame formulas solver next after ∧ Fits (classProfile record values.length profile) after ∧
      MergeStored saved ∧ (∀ value ∈ results, Cap Plain (classDepth record depth) value) ∧
      results.length = values.length ∧
      (∀ ambient symbol terms, EqualityNormalize.ClassSat (.node symbol terms) record.paths →
        (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
         All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)) ∧
      ∀ e p h m s n,
        classFuel record values.length profile ≤ e → classFuel record values.length profile ≤ p →
        classFuel record values.length profile ≤ h → classFuel record values.length profile ≤ m →
        classFuel record values.length profile ≤ s → classFuel record values.length profile ≤ n →
        SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo = .done results after saved := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, returned, numeric,
      retained, caps, length, done⟩ :=
    SourceCurrentConstrainedCapClassNumeric.complete depth formulas solver inventory record coherent active
      values before memo profile frame fits available domains physical covered merged memos valid bounded room
  refine ⟨results, after, saved, next, returned, numeric, retained, caps, length, ?_, ?_⟩
  · intro ambient symbol terms satisfied
    exact (receipt.language ambient symbol terms).2 satisfied
  · intro e p h m s n he hp hh hm hs hn
    exact SourceCurrentAllocatedClassWorkerStability.runClass_done_stable done he hp hh hm hs hn

#print axioms initial_contract
#check @initial_contract
end MicroCFTA.ClassNumericInitialKernels
