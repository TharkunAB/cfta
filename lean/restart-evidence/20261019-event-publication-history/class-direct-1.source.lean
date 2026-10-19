import MicroCFTA.SourceCurrentParentPublicationHistory
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# Actual publication intervals through chronological class folds

Each class starts from its actual tail return. Its physical publication
history contains the literal lower operations. No history is inferred from
the final heap or a future enclosing return.
-/
namespace MicroCFTA.SourceCurrentClassPublicationHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentNativeMuPublication (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fold" => SourceCurrentAllocatedClassPass.Fold
local notation "FoldReads" => SourceCurrentAllocatedClassPass.FoldReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- One supported actual class derives its complete physical publication interval. -/
theorem class_history {formulas solver record inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassEdits.Class (width := width) record inputs before memo results after saved}
    (reads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final)
    (inventory : Inventory) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    Nonempty (History before.native.machine.heap after.native.machine.heap) := by
  cases reads with
  | edit lower =>
    have initial := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record inputs
      before.native.machine.heap before memo ready admitted (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
    have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) inputs := by
      obtain ⟨entries,built⟩ := compiled_children record coherent active
      rw [built]
      exact compiled_safe record coherent inputs domains entries built
    exact SourceCurrentParentPublicationHistory.list lower available inventory
      (compiled_populated record) (compiled_allowed record) initial available safe valid

private def Law {formulas solver records inputs before memo results after saved}
    (_actual : Fold (width := width) records inputs before memo results after saved) (memos : Memos) : Prop :=
  ∀ inventory, (∀ record ∈ records, SourceEqualityClassOrder.Coherent record) →
    (∀ record ∈ records, EqualityNormalize.Nontrivial record.paths) → Ready before →
    SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before → Values before.native.machine.heap inputs →
    (∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs) →
    Stored before.native.machine.heap memo →
    (∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo) →
    EndpointMemoGateTrace.Valid before.native.machine.heap memos →
    Nonempty (History before.native.machine.heap after.native.machine.heap)

private theorem fold_law {formulas solver records inputs before memo results after saved memos final}
    {actual : Fold (width := width) records inputs before memo results after saved}
    (reads : FoldReads formulas solver actual memos final) : Law (formulas := formulas) (solver := solver) actual memos := by
  induction reads with
  | nil =>
    intro inventory coherent active ready admitted available domains stored covered valid
    exact ⟨.refl _⟩
  | @cons records inputs before memo middle step current record results after saved memos phaseMemos final
      tail head tailReads headReads ih =>
    intro inventory coherent active ready admitted available domains stored covered valid
    have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
    have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
    have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
    obtain ⟨phaseInventory,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory tailReads
      tailCoherent tailActive ready admitted available tailDomains stored covered valid
    obtain ⟨first⟩ := ih inventory tailCoherent tailActive ready admitted available tailDomains stored covered valid
    obtain ⟨last⟩ := class_history headReads phaseInventory
      (coherent record List.mem_cons_self) (active record List.mem_cons_self) receipt.ready receipt.admitted receipt.available
      (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
      receipt.stored receipt.covered receipt.globals.valid
    exact ⟨.trans first last⟩

/-- A completed actual right fold derives its history from the initial supported state. -/
theorem fold {formulas solver records inputs before memo results after saved memos final}
    {actual : Fold (width := width) records inputs before memo results after saved}
    (reads : FoldReads formulas solver actual memos final) (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    Nonempty (History before.native.machine.heap after.native.machine.heap) :=
  fold_law reads inventory coherent active ready admitted available domains stored covered valid

/-- Final empty propagation adds no publication after the actual fold. -/
theorem pass {formulas solver records inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Pass (width := width) records inputs before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final) (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    Nonempty (History before.native.machine.heap after.native.machine.heap) := by
  cases reads with
  | done reads => exact fold reads inventory coherent active ready admitted available domains stored covered valid

end MicroCFTA.SourceCurrentClassPublicationHistory
