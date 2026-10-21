import MicroCFTA.SourceCurrentConstrainedCapMixedClass
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# Finite-depth caps through the actual class right fold

Each head class captures the actual forest returned by its tail.
The earlier receipt transports selected domains to that new forest.
Final empty propagation changes no checked state or memo table.
These results verify supplied reads. They do not assert completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMixedClassPass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConstrainedCapMixedClass (classDepth)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable {width : Nat}

/-- The head transforms the depth produced by its actual recursive tail. -/
noncomputable def foldDepth : List SourceEqualityClassOrder.Record → Nat → Nat
  | [], depth => depth
  | record :: records, depth => classDepth record (foldDepth records depth)

/-- Literal empty propagation retains every supplied finite-depth cap. -/
theorem propagate_caps (depth : Nat) (values : List (Value Symbol Guard))
    (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∀ value ∈ EqualityLeafProjectionRuntimeEmpty.propagate values, Cap Plain depth value := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · intro value member
    obtain ⟨_, _, same⟩ := List.mem_map.mp member
    subst value
    exact .plain depth .empty
  · exact bounded

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem fold_caps (inventory : Inventory) (depth : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (current : Current before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap Plain depth value) :
    Current after ∧ MergeStored saved ∧ ∀ value ∈ results, Cap Plain (foldDepth records depth) value := by
  induction reads generalizing inventory with
  | nil => exact ⟨current, merged, bounded⟩
  | @cons records values before memo middle step currentMemo record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
      have retained := ih inventory tailCoherent tailActive ready admitted available tailDomains physical covered valid
        current merged bounded
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory first
        tailCoherent tailActive ready admitted available tailDomains physical covered valid
      obtain ⟨_lastInventory, _lastReceipt, currentAfter, mergedAfter, capsAfter⟩ :=
        SourceCurrentConstrainedCapMixedClass.verified formulas solver next record
          (coherent record List.mem_cons_self) (active record List.mem_cons_self) last
          receipt.ready receipt.admitted receipt.available
          (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
          receipt.stored receipt.covered receipt.globals.valid retained.1 retained.2.1 _ retained.2.2
      exact ⟨currentAfter, mergedAfter, capsAfter⟩

/-- Actual tail-first class reads retain their full receipt and both produced stores. -/
theorem fold (inventory : Inventory) (depth : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (current : Current before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧ ∀ value ∈ results, Cap Plain (foldDepth records depth) value := by
  have retained := fold_caps formulas solver inventory depth reads coherent active ready admitted available domains
    physical covered valid current merged bounded
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads coherent active
    ready admitted available domains physical covered valid
  exact ⟨next, receipt, retained⟩

/-- Final empty propagation retains the exact state, memo, receipt, and explicit depth bound. -/
theorem pass (inventory : Inventory) (depth : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (current : Current before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧ ∀ value ∈ results, Cap Plain (foldDepth records depth) value := by
  cases reads with
  | done lower =>
      obtain ⟨_next, _receipt, currentAfter, mergedAfter, capsAfter⟩ :=
        fold formulas solver inventory depth lower coherent active ready admitted available domains
          physical covered valid current merged bounded
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory (.done lower)
        coherent active ready admitted available domains physical covered valid
      exact ⟨next, receipt, currentAfter, mergedAfter, propagate_caps _ _ capsAfter⟩

end MicroCFTA.SourceCurrentConstrainedCapMixedClassPass
