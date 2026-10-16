import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability

/-!
# Numeric plans for the current class right fold

Each head plan inspects only an actual earlier tail return.
Induction derives the shorter tail's checks before it constructs that tail.
Literal worker uniqueness aligns any supplied earlier tail with that return.
No current head completion or future state invariant occurs in the plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassCapacity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Ranges Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNarrow (forest_domain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "ClassCapacity" => SourceCurrentAllocatedFiniteOrdinaryClassCapacity.ClassCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A head class receives a numeric plan only at its actual earlier tail's return. -/
inductive PassCapacity (bits : Nat) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Checked (bits + 2) → Memo → Prop where
  | nil : PassCapacity bits [] values before memo
  | cons (tail : PassCapacity bits records values before memo)
      (head : ∀ middle next current, Fold records values before memo middle next current →
        ClassCapacity bits record middle next current) :
      PassCapacity bits (record :: records) values before memo

/-- The tail uses the same original forest and warm state as the complete fold. -/
theorem PassCapacity.tail {bits : Nat} {record records values} {before : Checked (bits + 2)} {memo : Memo}
    (capacity : PassCapacity bits (record :: records) values before memo) :
    PassCapacity bits records values before memo := by cases capacity with | cons tail _ => exact tail

/-- Only an earlier actual tail selects the current class numeric plan. -/
theorem PassCapacity.head {bits : Nat} {record records values} {before after : Checked (bits + 2)} {memo saved : Memo}
    {results : List (Value Symbol Guard)} (capacity : PassCapacity bits (record :: records) values before memo)
    (tail : Fold records values before memo results after saved) : ClassCapacity bits record results after saved := by
  cases capacity with | cons _ head => exact head _ _ _ tail

private theorem fold_unique {width : Nat} {records values first second}
    {before after later : Checked width} {memo saved current : Memo}
    (one : Fold records values before memo first after saved)
    (two : Fold records values before memo second later current) : first = second ∧ after = later ∧ saved = current := by
  obtain ⟨e, p, h, m, s, n, completed⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete one
  obtain ⟨E, P, H, M, S, N, other⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete two
  exact SourceCurrentAllocatedClassWorkerStability.fold_done_unique
    (completed e p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (other E P H M S N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

/-- Initial invariants and causal numeric plans derive the existing right-fold range plan. -/
theorem ranges (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (memo : Memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (capacity : PassCapacity bits records values before memo) (memos : Memos)
    (valid : Valid before.native.machine.heap memos) : Ranges records values before memo := by
  induction capacity generalizing inventory memos with
  | nil => exact .nil
  | @cons records values before memo record tail head ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailRanges := ih inventory tailCoherent tailActive ready admitted available domain physical covered native merged memos valid
      refine .cons tailRanges ?_
      intro middle next current actualTail
      obtain ⟨chosen, after, saved, nextInventory, final, chosenTail, reads, receipt, nativeAfter, mergeAfter, related⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryClassPass.fold_finite formulas solver inventory tailRanges tailCoherent tailActive
          ready admitted available domain physical covered native merged memos valid
      obtain ⟨rfl, rfl, rfl⟩ := fold_unique chosenTail actualTail
      exact SourceCurrentAllocatedFiniteOrdinaryClassCapacity.class_ranges bits formulas solver nextInventory record
        (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) chosen after saved receipt.ready receipt.admitted
        receipt.available (forest_domain related) receipt.stored receipt.covered nativeAfter mergeAfter
        (head _ _ _ actualTail) final receipt.globals.valid

/-- The numeric tail plan constructs its own finite fold and every positional structural bound. -/
theorem fold_finite (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values} {before : Checked (bits + 2)} {memo : Memo}
    (capacity : PassCapacity bits records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Fold records values before memo results after saved,
      FoldReads formulas solver actual memos final ∧ Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  exact SourceCurrentAllocatedFiniteOrdinaryClassPass.fold_finite formulas solver inventory
    (ranges bits formulas solver inventory records values before memo coherent active ready admitted available domain physical
      covered native merged capacity memos valid)
    coherent active ready admitted available domain physical covered native merged memos valid

/-- Final propagation constructs the same full pass from initial facts and the numeric plan. -/
theorem finite (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values} {before : Checked (bits + 2)} {memo : Memo}
    (capacity : PassCapacity bits records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧ Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  exact SourceCurrentAllocatedFiniteOrdinaryClassPass.finite formulas solver inventory
    (ranges bits formulas solver inventory records values before memo coherent active ready admitted available domain physical
      covered native merged capacity memos valid)
    coherent active ready admitted available domain physical covered native merged memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassCapacity
