import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetCapacity

namespace MicroCFTA.FiniteOrdinaryTargetCapacityChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentAllocatedFiniteOrdinaryTargetCapacity
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalValid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A seed-only target has no native query and needs no numeric capacity premise. -/
theorem singleton_capacity (bits : Nat) (values : List (Value Symbol Guard)) (seed : List Int)
    (before : Checked (bits + 2)) (memo : Memo) : TargetCapacity bits values [seed] before memo := trivial

/-- Two operands check capacity only after their actual projection and merge prefixes. -/
theorem two_paths_capacity (bits : Nat) (values : List (Value Symbol Guard)) (seed path : List Int)
    (before : Checked (bits + 2)) (memo : Memo)
    (numeric : ∀ head middle current tail later saved,
      Operand path values before memo head middle current → Fold values seed [] middle current tail later saved →
      Capacity bits later) : TargetCapacity bits values [seed, path] before memo :=
  ⟨fun _ _ _ _ => trivial, numeric⟩

/-- The plan checks literal current supplies, with no current query return condition. -/
theorem exact_entry_supplies {bits : Nat} {values : List (Value Symbol Guard)} {seed path : List Int}
    {paths : List (List Int)} {before middle later : Checked (bits + 2)} {memo current saved : Memo}
    {head tail : Value Symbol Guard} (capacity : FoldCapacity bits values seed (path :: paths) before memo)
    (operand : Operand path values before memo head middle current)
    (rest : Fold values seed paths middle current tail later saved) :
    later.native.machine.heap.nodes.next ≤ 2 ^ bits ∧ later.native.machine.heap.edges.next ≤ 2 ^ (bits + 2) :=
  capacity.query operand rest

section Initial
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (bits : Nat) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : GlobalValid before.native.machine.heap memos)
include ready admitted available domain physicalStored mergeStored nativeStored covered valid

/-- A singleton constructs its own graph and all receipts without a word or capacity plan. -/
theorem singleton_finite (seed : List Int) :
    ∃ result after saved next final, ∃ actual : Target values [seed] before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values [seed] before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ DNode result :=
  SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.finite formulas solver inventory bits values [seed] before memo ready
    admitted available domain physicalStored mergeStored nativeStored covered
    (singleton_capacity bits values seed before memo) memos valid

/-- Earlier actual prefixes suffice to derive the next current query's full word plan. -/
theorem before_current_query (seed path : List Int) (paths : List (List Int))
    (capacity : FoldCapacity bits values seed (path :: paths) before memo)
    (head tail : Value Symbol Guard) (middle later : Checked (bits + 2)) (current saved : Memo)
    (operand : Operand path values before memo head middle current)
    (rest : Fold values seed paths middle current tail later saved) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain head tail)) later := by
  have derived := SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.fold_ranges formulas solver inventory bits values seed
    (path :: paths) before memo ready admitted available domain physicalStored mergeStored nativeStored covered capacity memos valid
  exact derived.2 _ _ _ _ _ _ operand rest

/-- The returned inventory, global validity, and cache certificates belong to the same actual target. -/
theorem same_actual_state (paths : List (List Int)) (capacity : TargetCapacity bits values paths before memo) :
    ∃ result after saved next final, ∃ actual : Target values paths before memo result after saved,
      TargetReads formulas solver actual memos final ∧ Ready after ∧ At formulas solver next after ∧
      GlobalValid after.native.machine.heap final ∧ Extends memo saved ∧
      PhysicalStored after.native.machine.heap saved ∧ MergeStored saved ∧ NativeStored after.native ∧
      Available after.native.machine.heap result ∧ DNode result := by
  obtain ⟨result, after, saved, next, final, actual, reads, receipt, merged, native, resultDomain⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.finite formulas solver inventory bits values paths before memo ready
      admitted available domain physicalStored mergeStored nativeStored covered capacity memos valid
  exact ⟨result, after, saved, next, final, actual, reads, receipt.ready, receipt.admitted, receipt.globals.valid,
    receipt.retained, receipt.stored, merged, native, receipt.available, resultDomain⟩

/-- Duplicate paths remain two actual operand occurrences in the constructed target. -/
theorem repeated_path_finite (path : List Int)
    (numeric : ∀ head middle current tail later saved,
      Operand path values before memo head middle current → Fold values path [] middle current tail later saved →
      Capacity bits later) :
    ∃ result after saved next final, ∃ actual : Target values [path, path] before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values [path, path] before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ DNode result :=
  SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.finite formulas solver inventory bits values [path, path] before memo ready
    admitted available domain physicalStored mergeStored nativeStored covered
    (two_paths_capacity bits values path path before memo numeric) memos valid
end Initial
end MicroCFTA.FiniteOrdinaryTargetCapacityChecks

#print axioms MicroCFTA.FiniteOrdinaryTargetCapacityChecks.singleton_capacity
#check @MicroCFTA.FiniteOrdinaryTargetCapacityChecks.singleton_capacity
#print axioms MicroCFTA.FiniteOrdinaryTargetCapacityChecks.two_paths_capacity
#check @MicroCFTA.FiniteOrdinaryTargetCapacityChecks.two_paths_capacity
#print axioms MicroCFTA.FiniteOrdinaryTargetCapacityChecks.exact_entry_supplies
#check @MicroCFTA.FiniteOrdinaryTargetCapacityChecks.exact_entry_supplies
#print axioms MicroCFTA.FiniteOrdinaryTargetCapacityChecks.singleton_finite
#check @MicroCFTA.FiniteOrdinaryTargetCapacityChecks.singleton_finite
#print axioms MicroCFTA.FiniteOrdinaryTargetCapacityChecks.before_current_query
#check @MicroCFTA.FiniteOrdinaryTargetCapacityChecks.before_current_query
#print axioms MicroCFTA.FiniteOrdinaryTargetCapacityChecks.same_actual_state
#check @MicroCFTA.FiniteOrdinaryTargetCapacityChecks.same_actual_state
#print axioms MicroCFTA.FiniteOrdinaryTargetCapacityChecks.repeated_path_finite
#check @MicroCFTA.FiniteOrdinaryTargetCapacityChecks.repeated_path_finite
