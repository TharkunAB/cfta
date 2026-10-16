import MicroCFTA.SourceCurrentAllocatedSharedTargetState
namespace MicroCFTA.AllocatedSharedTargetStateKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedSharedTargetState
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceEqualityClassTarget (operandPaths)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Class initialization clears only slots. It keeps the exact checked state, equality operations, and merge memo.
example (checked : Checked width) (memo : Memo) :
 (initial checked memo).checked = checked ∧ (initial checked memo).checked.operations = checked.operations ∧
 (initial checked memo).memo = memo ∧ ∀ path, (initial checked memo).targets path = none :=
 ⟨rfl, rfl, rfl, fun _ => rfl⟩

section Slots
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
 {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
 {before after : Heap} {memo saved : Memo} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
 (receipt : SlotReceipt width formulas solver record values before memo path value)
 (keeps : SourceEqualityRequiredCache.Keeps before after) (retained : Extends memo saved)

-- Actual old slot receipts give closed available values after heap and merge-table growth.
example : Available after value ∧ value.free = [] := (receipt.grows keeps retained).available

-- Selected-term meaning needs no current inventory, At, or current cache coverage premise.
example (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths) :
 SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value :=
 (receipt.grows keeps retained).included coherent active
end Slots

section Current
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
 {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap}
 {before : Shared width} (ready : Ready formulas solver inventory record values base before)

-- Constructor effects derive the same current inventory's admission and retain each old slot's availability.
example (after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula)
 (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) after)
 (path : EqualityNormalize.Path) (value : Value Symbol Guard) (found : before.targets path = some value) :
 let reached := SourceCurrentAllocatedQueryMemo.advancePhysical before.checked after
 At formulas solver inventory reached ∧ Available reached.native.machine.heap value ∧ value.free = [] := by
 have current := ready.physical after effects
 have slot := current.receipts path value found
 exact ⟨current.admitted, slot.available⟩

-- An actual checked query may expand its inventory while the literal old target slot remains usable.
example (next : Inventory) (checked : Checked width) (nextReady : SourceCurrentConjunctionClassScan.Ready checked)
 (nextAt : At formulas solver next checked)
 (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical checked))
 (path : EqualityNormalize.Path) (value : Value Symbol Guard) (found : before.targets path = some value) :
 Ready formulas solver next record values base (advance before checked) ∧
 SlotReceipt width formulas solver record values checked.native.machine.heap before.memo path value := by
 have advanced := ready.advance next checked nextReady nextAt effects
 exact ⟨advanced, advanced.receipts path value found⟩

-- Storing an actual target retains every distinct old slot's historical graph and language receipt.
example {next : Inventory} (path : EqualityNormalize.Path) (member : path ∈ record.paths)
 {value : Value Symbol Guard} {after : Checked width} {saved : Memo} {memos final : Memos}
 (actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path) before.checked before.memo value after saved)
 (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
 (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values (operandPaths record.paths path)
  before.checked before.memo value after saved memos final)
 (other : EqualityNormalize.Path) (target : Value Symbol Guard) (different : other ≠ path)
 (found : before.targets other = some target) :
 SlotReceipt width formulas solver record values after.native.machine.heap saved other target := by
 have current := ready.store path member actual reads receipt
 apply current.receipts other target
 simpa only [store, put, different, ite_false] using found

-- The newly stored slot has closed availability and selected meaning at the computed inventory.
example {next : Inventory} (path : EqualityNormalize.Path) (member : path ∈ record.paths)
 {value : Value Symbol Guard} {after : Checked width} {saved : Memo} {memos final : Memos}
 (actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path) before.checked before.memo value after saved)
 (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
 (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values (operandPaths record.paths path)
  before.checked before.memo value after saved memos final)
 (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths) :
 At formulas solver next after ∧ value.free = [] ∧
 SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value := by
 have current := ready.store path member actual reads receipt
 have present : (store before path value after saved).targets path = some value := by simp only [store, put, ite_true]
 have slot := current.receipts path value present
 exact ⟨current.admitted, slot.available.2, slot.included coherent active⟩
end Current
end MicroCFTA.AllocatedSharedTargetStateKernels
