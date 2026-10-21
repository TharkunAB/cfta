import MicroCFTA.SourceCurrentClassPositiveAncestry
import MicroCFTA.SourceCurrentClassCorridorChronology

/-!
# Positive ancestry through completed chronological class reads

Each head class captures the actual tail return. Its stores and history
come from that same tail. Exact intermediate lookups compose the positive
paths under the original record family. Empty propagation adds no call.
-/
namespace MicroCFTA.SourceCurrentClassPositiveChronology
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceEqualityProjectionGraph (select)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentRequiredRawCorridor (RawCorridor)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNormalizedChildSeparation (Rel)
open SourceCurrentNativeMuPublication (History)
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
local notation "NativeSupport" => SourceCurrentNativeRequestPositivePositions.Support
local notation "MergeSupport" => SourceCurrentMergePositivePosition.Support
private def Preserves (original result : Node) : Prop :=
  ∀ path, RawCorridor path original → RawCorridor path result
private def Masks (record : SourceEqualityClassOrder.Record) (values : List Node) : Prop :=
  ∀ index path, index::path ∈ record.paths → ∀ value,
    select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value
private def Back (records : List SourceEqualityClassOrder.Record) (values results : List Node) : Prop :=
  ∀ outputIndex result, results[outputIndex]? = some result → ∀ residual, PositiveAt result residual →
    ∃ inputIndex originalPath original, values[inputIndex]? = some original ∧ PositiveAt original originalPath ∧
      Rel (records.map SourceEqualityClassOrder.Record.paths) (outputIndex::residual) (inputIndex::originalPath)

private theorem rel_mono {classes others : EqualityNormalize.Constraints}
    (included : ∀ paths ∈ classes, paths ∈ others) {left right} (related : Rel classes left right) : Rel others left right := by
  induction related with
  | refl path => exact .refl path
  | member paths selected left right first second suffix =>
    exact .member paths (included paths selected) left right first second suffix
  | trans _ _ first second => exact .trans first second
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
  obtain ⟨original,selected,retained⟩ := SourceEqualityProjectionLanguage.all₂_signed related (Int.ofNat index) value found
  exact retained (path.map Int.ofNat) (masks index path included original selected)
private theorem propagate_relation (values : List Node) :
    All₂ Preserves values (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · rename_i condition
    clear condition
    induction values with
    | nil => exact .nil
    | cons value values ih => exact .cons (fun path _ => .full path .empty ⟨0,.plain 0 .empty⟩) ih
  · exact relation_refl values
private theorem propagate_back {records values results} (back : Back records values results) :
    Back records values (EqualityLeafProjectionRuntimeEmpty.propagate results) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · intro index result found path positive
    have member := List.mem_of_getElem? found
    change result ∈ results.map (fun _ => (Value.empty : Node)) at member
    obtain ⟨original,_included,same⟩ := List.mem_map.mp member
    cases same
    cases positive
  · exact back

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
    (current : Current before) (merged : MergeStored memo) (masks : ∀ record ∈ records, Masks record values)
    (supported : NativeSupport before.native.machine.heap before.native) (causal : History empty before.native.machine.heap)
    (positiveMemo : MergeSupport memo) :
    Current after ∧ MergeStored saved ∧ All₂ Preserves values results ∧
      NativeSupport after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) ∧
      MergeSupport saved ∧ Back records values results := by
  induction reads generalizing inventory with
  | nil =>
    refine ⟨current,merged,relation_refl _,supported,⟨causal⟩,positiveMemo,?_⟩
    intro index result found path positive
    exact ⟨index,path,result,found,positive,.refl _⟩
  | @cons records values before memo middle step currentMemo record results after saved memos stepMemos final tail head first last ih =>
    have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
    have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
    have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
    obtain ⟨tailCurrent,tailMerged,tailCorridors,tailSupported,⟨tailCausal⟩,tailPositive,tailBack⟩ :=
      ih inventory tailCoherent tailActive ready admitted available tailDomains physical covered valid current merged
        (fun own member => masks own (List.mem_cons_of_mem record member)) supported causal positiveMemo
    obtain ⟨next,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory first
      tailCoherent tailActive ready admitted available tailDomains physical covered valid
    obtain ⟨_lastInventory,_lastReceipt,currentAfter,mergedAfter,corridorsAfter,supportedAfter,causalAfter,positiveAfter,headBack⟩ :=
      SourceCurrentClassPositiveAncestry.class_reads formulas solver next record
        (coherent record List.mem_cons_self) (active record List.mem_cons_self) last
        receipt.ready receipt.admitted receipt.available
        (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
        receipt.stored receipt.covered receipt.globals.valid tailCurrent tailMerged
        (masks_selected tailCorridors record (masks record List.mem_cons_self)) tailSupported tailCausal tailPositive
    refine ⟨currentAfter,mergedAfter,relation_trans tailCorridors corridorsAfter,supportedAfter,causalAfter,positiveAfter,?_⟩
    intro outputIndex result found residual positive
    obtain ⟨middleIndex,middlePath,middleValue,middleFound,middlePositive,headRelated⟩ := headBack outputIndex result found residual positive
    obtain ⟨inputIndex,originalPath,original,originalFound,originalPositive,tailRelated⟩ :=
      tailBack middleIndex middleValue middleFound middlePath middlePositive
    refine ⟨inputIndex,originalPath,original,originalFound,originalPositive,?_⟩
    have headFull : Rel ((record::records).map SourceEqualityClassOrder.Record.paths)
        (outputIndex::residual) (middleIndex::middlePath) :=
      rel_mono (by intro paths member; cases List.mem_singleton.mp member; exact List.mem_cons_self) headRelated
    have tailFull : Rel ((record::records).map SourceEqualityClassOrder.Record.paths)
        (middleIndex::middlePath) (inputIndex::originalPath) :=
      rel_mono (fun _ member => List.mem_cons_of_mem _ member) tailRelated
    exact .trans headFull tailFull

/-- Completed tail-first classes retain the same positive stores and literal entry ancestry. -/
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
    (masks : ∀ record ∈ records, ∀ index path, index::path ∈ record.paths → ∀ value,
      select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value)
    (supported : NativeSupport before.native.machine.heap before.native) (causal : History empty before.native.machine.heap)
    (positiveMemo : MergeSupport memo) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧
      All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results ∧
      NativeSupport after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) ∧ MergeSupport saved ∧
      ∀ outputIndex result, results[outputIndex]? = some result → ∀ residual, PositiveAt result residual →
        ∃ inputIndex originalPath original, values[inputIndex]? = some original ∧ PositiveAt original originalPath ∧
          Rel (records.map SourceEqualityClassOrder.Record.paths) (outputIndex::residual) (inputIndex::originalPath) := by
  have retained := fold_law formulas solver inventory reads coherent active ready admitted available domains physical covered valid
    current merged masks supported causal positiveMemo
  obtain ⟨next,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads coherent active
    ready admitted available domains physical covered valid
  exact ⟨next,receipt,retained⟩

/-- Actual final empty propagation retains the stores and cannot create a positive occurrence. -/
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
    (masks : ∀ record ∈ records, ∀ index path, index::path ∈ record.paths → ∀ value,
      select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value)
    (supported : NativeSupport before.native.machine.heap before.native) (causal : History empty before.native.machine.heap)
    (positiveMemo : MergeSupport memo) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧
      All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results ∧
      NativeSupport after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) ∧ MergeSupport saved ∧
      ∀ outputIndex result, results[outputIndex]? = some result → ∀ residual, PositiveAt result residual →
        ∃ inputIndex originalPath original, values[inputIndex]? = some original ∧ PositiveAt original originalPath ∧
          Rel (records.map SourceEqualityClassOrder.Record.paths) (outputIndex::residual) (inputIndex::originalPath) := by
  cases reads with
  | done lower =>
    obtain ⟨_next,_receipt,currentAfter,mergedAfter,related,supportedAfter,causalAfter,positiveAfter,back⟩ :=
      fold formulas solver inventory lower coherent active ready admitted available domains physical covered valid current merged masks
        supported causal positiveMemo
    obtain ⟨next,receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory (.done lower) coherent active
      ready admitted available domains physical covered valid
    exact ⟨next,receipt,currentAfter,mergedAfter,relation_trans related (propagate_relation _),
      supportedAfter,causalAfter,positiveAfter,propagate_back back⟩

end MicroCFTA.SourceCurrentClassPositiveChronology

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentClassPositiveChronology.fold
#print MicroCFTA.SourceCurrentClassPositiveChronology.fold
#print axioms MicroCFTA.SourceCurrentClassPositiveChronology.fold

#check @MicroCFTA.SourceCurrentClassPositiveChronology.pass
#print MicroCFTA.SourceCurrentClassPositiveChronology.pass
#print axioms MicroCFTA.SourceCurrentClassPositiveChronology.pass

