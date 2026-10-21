import MicroCFTA.SourceCurrentClassEndpointCorridors
import MicroCFTA.SourceCurrentAllocatedClassPass
import MicroCFTA.SourceCurrentClassPassPhaseLineage

/-!
# Raw endpoint corridors through chronological class folds

Every class captures the actual tail return. The tail receipt supplies its
readiness and domains. The ordered corridor relation supplies every original
selected mask at that same capture. Final propagation changes no cache.
-/
namespace MicroCFTA.SourceCurrentClassCorridorChronology
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceEqualityProjectionGraph (select)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentRequiredRawCorridor (RawCorridor)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
private def Preserves (original result : Node) : Prop :=
  ∀ path, RawCorridor path original → RawCorridor path result
private def Masks (record : SourceEqualityClassOrder.Record) (values : List Node) : Prop :=
  ∀ index path, index :: path ∈ record.paths → ∀ value,
    select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value

private theorem relation_refl (values : List Node) : All₂ Preserves values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (fun _ raw => raw) ih

private theorem relation_trans {values middle results : List Node}
    (first : All₂ Preserves values middle) (last : All₂ Preserves middle results) : All₂ Preserves values results := by
  induction first generalizing results with
  | nil => cases last; exact .nil
  | cons first rest ih =>
    cases last with
    | cons second tail => exact .cons (fun path raw => second path (first path raw)) (ih tail)

private theorem masks_selected {values results : List Node} (related : All₂ Preserves values results)
    (record : SourceEqualityClassOrder.Record) (masks : Masks record values) : Masks record results := by
  intro index path included value found
  obtain ⟨original, selected, retained⟩ := SourceEqualityProjectionLanguage.all₂_signed related (Int.ofNat index) value found
  exact retained (path.map Int.ofNat) (masks index path included original selected)

private theorem propagate_relation (values : List Node) :
    All₂ Preserves values (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · rename_i condition
    clear condition
    induction values with
    | nil => exact .nil
    | cons value values ih => exact .cons (fun path _ => .full path .empty ⟨0, .plain 0 .empty⟩) ih
  · exact relation_refl values

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem fold_law (inventory : Inventory)
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
    (masks : ∀ record ∈ records, Masks record values) :
    Current after ∧ MergeStored saved ∧ All₂ Preserves values results := by
  induction reads generalizing inventory with
  | nil => exact ⟨current, merged, relation_refl _⟩
  | @cons records values before memo middle step currentMemo record results after saved memos stepMemos final tail head first last ih =>
    have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
    have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
    have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
    have retained := ih inventory tailCoherent tailActive ready admitted available tailDomains physical covered valid
      current merged (fun own member => masks own (List.mem_cons_of_mem record member))
    obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory first
      tailCoherent tailActive ready admitted available tailDomains physical covered valid
    obtain ⟨_lastInventory, _lastReceipt, currentAfter, mergedAfter, related⟩ :=
      SourceCurrentClassEndpointCorridors.class_reads formulas solver next record
        (coherent record List.mem_cons_self) (active record List.mem_cons_self) last
        receipt.ready receipt.admitted receipt.available
        (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
        receipt.stored receipt.covered receipt.globals.valid retained.1 retained.2.1
        (masks_selected retained.2.2 record (masks record List.mem_cons_self))
    exact ⟨currentAfter, mergedAfter, relation_trans retained.2.2 related⟩

/-- Actual tail-first class reads retain every original corridor and both produced stores. -/
theorem fold (inventory : Inventory)
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
    (masks : ∀ record ∈ records, ∀ index path, index :: path ∈ record.paths → ∀ value,
      select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧
      All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results := by
  have retained := fold_law formulas solver inventory reads coherent active ready admitted available domains
    physical covered valid current merged masks
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads coherent active
    ready admitted available domains physical covered valid
  exact ⟨next, receipt, retained⟩

/-- Final empty propagation retains the exact state, memo and every original corridor. -/
theorem pass (inventory : Inventory)
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
    (masks : ∀ record ∈ records, ∀ index path, index :: path ∈ record.paths → ∀ value,
      select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧
      All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results := by
  cases reads with
  | done lower =>
    obtain ⟨_next, _receipt, currentAfter, mergedAfter, related⟩ := fold formulas solver inventory lower coherent active
      ready admitted available domains physical covered valid current merged masks
    obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory (.done lower)
      coherent active ready admitted available domains physical covered valid
    exact ⟨next, receipt, currentAfter, mergedAfter, relation_trans related (propagate_relation _)⟩

/-- The same indexed class occurrence receives the actual tail's corridor relation and stores. -/
theorem indexed_phase (inventory : Inventory)
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
    (masks : ∀ record ∈ records, ∀ index path, index :: path ∈ record.paths → ∀ value,
      select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value)
    {index : Nat} {record : SourceEqualityClassOrder.Record} (selected : records[index]? = some record) :
    ∃ phaseValues phaseState phaseMemo phaseMemos headValues headState headMemo headMemos,
    ∃ tail : Fold (records.drop (index + 1)) values before memo phaseValues phaseState phaseMemo,
    ∃ call : Class record phaseValues phaseState phaseMemo headValues headState headMemo,
    ∃ later : Fold (records.take index) headValues headState headMemo results after saved,
    ∃ phaseInventory,
      FoldReads formulas solver tail memos phaseMemos ∧
      ClassReads formulas solver call phaseMemos headMemos ∧
      FoldReads formulas solver later headMemos final ∧
      Receipt formulas solver phaseInventory (records.drop (index + 1)) values before memo
        phaseValues phaseState phaseMemo memos phaseMemos ∧
      Current phaseState ∧ MergeStored phaseMemo ∧
      All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values phaseValues := by
  obtain ⟨phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo, headMemos,
    tail, call, later, tailReads, callReads, laterReads⟩ := SourceCurrentClassPassPhaseLineage.fold_indexed reads selected
  obtain ⟨next, receipt, phaseCurrent, phaseMerged, related⟩ := fold formulas solver inventory tailReads
    (fun own member => coherent own (List.mem_of_mem_drop member))
    (fun own member => active own (List.mem_of_mem_drop member)) ready admitted available
    (fun own member => domains own (List.mem_of_mem_drop member)) physical covered valid current merged
    (fun own member => masks own (List.mem_of_mem_drop member))
  exact ⟨phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo, headMemos,
    tail, call, later, next, tailReads, callReads, laterReads, receipt, phaseCurrent, phaseMerged, related⟩

end MicroCFTA.SourceCurrentClassCorridorChronology
