import MicroCFTA.SourceCurrentAllocatedProbeEdits
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# Filtered probes through the actual current class right fold

Each class captures the literal forest returned by its tail. The compiled
selected-path domains derive its edit inputs. Empty propagation adds no
constructor work. Finite range plans construct the same actual reads.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeClassPass
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassPass
open SourceEqualityProjectionPathDomain (ForestClosed)
open InternedFreshOrdinaryProbeHeap (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Compiled class execution derives probes from its original selected paths. -/
theorem class_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (probes : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases reads with
  | edit lower =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready
        formulas solver inventory record values before.native.machine.heap before memo ready admitted
        (pure_keeps _ ready.semantic.ready) stored covered
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      exact SourceCurrentAllocatedProbeEdits.list_heap lower (compiled_populated record) (compiled_allowed record)
        initialReady available safe valid available probes

/-- Actual right folds retain probes through the tail before the head class. -/
theorem fold_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (probes : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  induction reads generalizing inventory with
  | nil => exact probes
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem _ member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem _ member)
      have tailDomains := fun own member => domains own (List.mem_cons_of_mem _ member)
      have middleProbes := ih inventory tailCoherent tailActive ready admitted available tailDomains stored covered valid probes
      obtain ⟨next, firstReceipt⟩ := Fold.verified formulas solver inventory first tailCoherent tailActive
        ready admitted available tailDomains stored covered valid
      exact class_heap formulas solver next record (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        last firstReceipt.ready firstReceipt.admitted firstReceipt.available
        (fun path member => firstReceipt.domains _ (domains _ List.mem_cons_self path member))
        firstReceipt.stored firstReceipt.covered firstReceipt.globals.valid middleProbes

/-- Final empty propagation retains the actual returned constructor heap. -/
theorem pass_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (probes : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases reads with
  | done reads => exact fold_heap formulas solver inventory reads coherent active ready admitted available domains stored covered valid probes

/-- Actual-prefix ranges construct a finite pass and its probe invariant together. -/
theorem pass_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values} {before : Checked width} {memo : Memo}
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) (probes : Heap before.native.machine.heap) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before memo results after saved memos final ∧
      Heap after.native.machine.heap := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt⟩ := SourceCurrentAllocatedClassPass.pass_complete
    formulas solver inventory ranges coherent active ready admitted available domains stored covered memos valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt,
    pass_heap formulas solver inventory reads coherent active ready admitted available domains stored covered valid probes⟩

end MicroCFTA.SourceCurrentAllocatedProbeClassPass
