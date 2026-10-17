import MicroCFTA.SourceCurrentConstrainedCapClassForecast
import MicroCFTA.SourceCurrentEditListNumeric
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability
import MicroCFTA.SourceCurrentAllocatedClassWorker

/-!
# Complete class edits from initial numeric room

The class captures its literal entry forest and starts fresh target slots.
The native tables, equality operations, and Merge memo remain warm.
The finite compiled editor constructs its own actual execution. Its returned
Frame determines the same inventory in the complete old class receipt.
-/
namespace MicroCFTA.SourceCurrentClassNumeric
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "classProfile" => SourceCurrentConstrainedCapClassForecast.classProfile
local notation "classFuel" => SourceCurrentConstrainedCapClassForecast.classFuel
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial selected domains and one final-profile room test construct the full class return. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (room : Room bits (classProfile record values.length profile)) :
    ∃ results after saved next final, ∃ actual : Class record values before memo results after saved,
      ClassReads formulas solver actual memos final ∧
      Receipt formulas solver next record values before memo results after saved memos final ∧
      Frame formulas solver next after ∧ Fits (classProfile record values.length profile) after ∧
      results.length = values.length ∧
      SourceCurrentAllocatedClassWorker.runClass
        (classFuel record values.length profile) (classFuel record values.length profile)
        (classFuel record values.length profile) (classFuel record values.length profile)
        (classFuel record values.length profile) (classFuel record values.length profile)
        record values before memo = .done results after saved ∧
      ∀ e p h m c n, classFuel record values.length profile ≤ e → classFuel record values.length profile ≤ p →
        classFuel record values.length profile ≤ h → classFuel record values.length profile ≤ m →
        classFuel record values.length profile ≤ c → classFuel record values.length profile ≤ n →
        SourceCurrentAllocatedClassWorker.runClass e p h m c n record values before memo = .done results after saved := by
  have ready := SourceCurrentAllocatedSharedTargetState.initial_ready
    formulas solver inventory record values before.native.machine.heap before memo frame.ready frame.admitted
    (SourceEqualityRequiredCache.pure_keeps _ frame.ready.semantic.ready) physical covered
  have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    rw [built]
    exact compiled_safe record coherent values domains entries built
  have reserved : SourceCurrentEditListNumeric.Reserved bits record values.length
      (compiled record) values.length profile := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    simpa only [SourceCurrentEditListNumeric.Reserved, built, SourceCurrentConstrainedCapClassForecast.classProfile] using room
  obtain ⟨results, shared, next, final, lower, lowerReads, lowerReceipt, returned, numeric, done⟩ :=
    SourceCurrentEditListNumeric.complete formulas solver inventory record values
      before.native.machine.heap (SourceCurrentAllocatedSharedTargetState.initial before memo) profile ready frame fits
      available domains coherent active (compiled record) (compiled_populated record) (compiled_allowed record)
      values available safe memos valid reserved
  have actual : Class record values before memo results shared.checked shared.memo := .edit lower
  have reads : ClassReads formulas solver actual memos final := .edit lowerReads
  obtain ⟨_previousInventory, previous⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver inventory record
    coherent active reads frame.ready frame.admitted available domains physical covered valid
  have receipt : Receipt formulas solver next record values before memo results shared.checked shared.memo memos final :=
    ⟨previous.ready, returned.admitted, previous.effects, previous.extension, previous.stored, previous.covered,
      previous.available, previous.transport, previous.domains, previous.retained, previous.globals, previous.language⟩
  refine ⟨results, shared.checked, shared.memo, next, final, actual, reads, receipt, returned,
    numeric, (All₂.length_eq lowerReceipt.transport).symm, ?_⟩
  have returnedWorker : SourceCurrentAllocatedClassWorker.runClass
      (classFuel record values.length profile) (classFuel record values.length profile)
      (classFuel record values.length profile) (classFuel record values.length profile)
      (classFuel record values.length profile) (classFuel record values.length profile)
      record values before memo = .done results shared.checked shared.memo := by
    simp only [SourceCurrentAllocatedClassWorker.runClass, SourceCurrentConstrainedCapClassForecast.classFuel, done]
  exact ⟨returnedWorker, fun _ _ _ _ _ _ he hp hh hm hc hn =>
    SourceCurrentAllocatedClassWorkerStability.runClass_done_stable returnedWorker he hp hh hm hc hn⟩

end MicroCFTA.SourceCurrentClassNumeric
