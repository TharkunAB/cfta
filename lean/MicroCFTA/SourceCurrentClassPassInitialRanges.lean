import MicroCFTA.SourceCurrentClassPassNumeric
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
import MicroCFTA.SourceCurrentEditListNumericRanges

/-!
# Class pass ranges from current numeric reservations

The tail runs before the head class. Numeric completion identifies each
actual completed tail with its current resource receipt. This proof uses
no Scan graph or future class range supplier.
-/
namespace MicroCFTA.SourceCurrentClassPassInitialRanges
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedClassEditPlan
open SourceEqualityClassOrder (Record Coherent)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Current class data and its reserved profile derive the actual edit range plan. -/
theorem class_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : Record) (coherent : Coherent record) (active : Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (room : Room bits (SourceCurrentConstrainedCapClassForecast.classProfile record values.length profile)) :
    SourceCurrentAllocatedClassEdits.ClassRanges record values before memo := by
  have ready := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
    before.native.machine.heap before memo frame.ready frame.admitted
    (SourceEqualityRequiredCache.pure_keeps _ frame.ready.semantic.ready) physical covered
  have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    rw [built]
    exact compiled_safe record coherent values domains entries built
  have reserved : SourceCurrentEditListNumeric.Reserved bits record values.length
      (compiled record) values.length profile :=
    SourceCurrentConstrainedCapClassForecast.class_reserved bits record values.length profile room
  exact SourceCurrentEditListNumericRanges.list_ranges formulas solver inventory record values
    before.native.machine.heap (SourceCurrentAllocatedSharedTargetState.initial before memo) profile
    ready frame fits available domains coherent active (compiled record) (compiled_populated record)
    (compiled_allowed record) values available safe memos valid reserved

private theorem fold_unique {records values first second}
    {before after later : Checked width} {memo saved current : Memo}
    (one : SourceCurrentAllocatedClassPass.Fold records values before memo first after saved)
    (two : SourceCurrentAllocatedClassPass.Fold records values before memo second later current) :
    first = second ∧ after = later ∧ saved = current := by
  obtain ⟨e, p, h, m, s, n, completed⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete one
  obtain ⟨E, P, H, M, S, N, other⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete two
  exact SourceCurrentAllocatedClassWorkerStability.fold_done_unique
    (completed e p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (other E P H M S N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

/-- Current fold data derive every actual tail-first class range plan. -/
theorem pass_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List Record)
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records values.length profile) :
    SourceCurrentAllocatedClassPass.Ranges records values before memo := by
  induction records generalizing inventory values before memo profile memos with
  | nil => exact .nil
  | cons record records ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
      have tailRoom := SourceCurrentConstrainedCapClassForecast.reserved_tail bits record records values.length profile reserved
      refine .cons (ih inventory tailCoherent tailActive values before memo profile frame fits available
        tailDomains physical covered memos valid tailRoom) ?_
      intro supplied step current actualTail
      obtain ⟨middle, next, saved, tailInventory, final, chosen, _reads, receipt, returned, numeric,
          sameLength, _done, _stable⟩ :=
        SourceCurrentClassPassNumeric.fold formulas solver inventory records tailCoherent tailActive values
          before memo profile frame fits available tailDomains physical covered memos valid tailRoom
      obtain ⟨rfl, rfl, rfl⟩ := fold_unique chosen actualTail
      have room : Room bits (SourceCurrentConstrainedCapClassForecast.classProfile record middle.length
          (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile)) := by
        simpa only [sameLength] using
          SourceCurrentConstrainedCapClassForecast.reserved_head bits record records values.length profile reserved
      exact class_ranges formulas solver tailInventory record (coherent _ List.mem_cons_self)
        (active _ List.mem_cons_self) middle next saved
        (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile)
        returned numeric receipt.available
        (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
        receipt.stored receipt.covered final receipt.globals.valid room

end MicroCFTA.SourceCurrentClassPassInitialRanges
