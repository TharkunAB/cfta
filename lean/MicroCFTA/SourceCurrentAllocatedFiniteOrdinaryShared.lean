import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCache
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequired

/-!
# Finite ordinary admission in class-local target state

The three actual tables retain separate structural certificates. Native
results are tied to their captured request. Merge results are tied to their
captured original. Each target slot contains a finite ordinary value.
Initialization clears slots only. Constructor advancement retains all slots
and merge entries. A new target slot requires its actual derived domain.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryShared
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedSharedTargetState (State initial advance store)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "MergeMemo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
variable {width : Nat}

/-- Actual shared state retains causal structural facts for its three result tables. -/
structure Stored (state : State width) : Prop where
  native : NativeStored state.checked.native
  merge : MergeStored state.memo
  slots : ∀ path value, state.targets path = some value → DNode value

/-- A class starts with empty target slots and its existing admitted native and merge tables. -/
theorem initial_stored (checked : Checked width) (memo : MergeMemo)
    (native : NativeStored checked.native) (merged : MergeStored memo) : Stored (initial checked memo) :=
  ⟨native, merged, by intro path value absent; cases absent⟩

/-- Native execution retains class slots and the same completed merge entries. -/
theorem advance_stored (state : State width) (checked : Checked width)
    (stored : Stored state) (native : NativeStored checked.native) : Stored (advance state checked) :=
  ⟨native, stored.merge, stored.slots⟩

/-- Constructor-only advancement retains all three structural table certificates. -/
theorem advance_heap_stored (state : State width)
    (heap : InternedConstructorTemplates.State Symbol Guard) (stored : Stored state) :
    Stored (advance state (SourceCurrentAllocatedQueryMemo.advancePhysical state.checked ⟨heap, state.checked.operations⟩)) :=
  advance_stored state _ stored (SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ stored.native)

/-- A completed target stores its derived ordinary domain at the actual target slot. -/
theorem store_stored (state : State width) (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (checked : Checked width) (memo : MergeMemo) (stored : Stored state)
    (native : NativeStored checked.native) (merged : MergeStored memo) (domain : DNode value) :
    Stored (store state path value checked memo) := by
  refine ⟨native, merged, ?_⟩
  intro other result found
  by_cases same : other = path
  · subst other
    have resultSame : value = result := Option.some.inj (by simpa only [store, put, ite_true] using found)
    exact resultSame ▸ domain
  · exact stored.slots other result (by simpa only [store, put, same, ite_false] using found)

open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Force" => SourceCurrentAllocatedSharedTargetForce.Force
local notation "ForceRanges" => SourceCurrentAllocatedSharedTargetForce.ForceRanges
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf
local notation "LeafRanges" => SourceCurrentAllocatedSharedTargetLeaf.Ranges
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalValid" => EndpointMemoGateTrace.Valid

section Producers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
variable {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {input value result : Value Symbol Guard}

private theorem selected_domains
    (ready : Ready formulas solver inventory record values base before)
    (known : Values base values) (domain : DChildren values) :
    ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values := by
  intro path _
  exact SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.checked.semantic values
    (fun value member => ready.captured.available value (known value member)) domain _

private theorem force_structure (actual : Force record values path before value after)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    Stored after ∧ DNode value := by
  cases actual with
  | hit present => exact ⟨stored, stored.slots path value present⟩
  | miss absent target =>
      obtain ⟨_, _, _, _, merged, native, resultDomain⟩ := SourceCurrentAllocatedFiniteOrdinaryTarget.target
        formulas solver inventory target ready.checked ready.admitted
        (fun value member => ready.captured.available value (known value member)) domain
        ready.stored stored.merge stored.native ready.covered (ranges absent) memos valid
      exact ⟨store_stored before path value _ _ stored native merged resultDomain, resultDomain⟩

/-- Actual forcing derives its result domain and retains all three structural tables. -/
theorem force (actual : Force record values path before value after)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    ∃ next final, ForceReceipt formulas solver next record values base path before value after memos final ∧
      Stored after ∧ DNode value := by
  obtain ⟨next, final, receipt⟩ := actual.verified formulas solver inventory ready known
    (selected_domains formulas solver inventory ready known domain) coherent active member ranges memos valid
  exact ⟨next, final, receipt, force_structure formulas solver inventory actual ready known domain stored ranges memos valid⟩

/-- Initial class facts and reached checks construct the force and its structural result. -/
theorem force_finite (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    ∃ value after next final, ForceReceipt formulas solver next record values base path before value after memos final ∧
      Stored after ∧ DNode value := by
  obtain ⟨value, after, next, final, actual, receipt⟩ := SourceCurrentAllocatedSharedTargetForce.complete
    formulas solver inventory record values base before ready known (selected_domains formulas solver inventory ready known domain)
    coherent active path member ranges memos valid
  exact ⟨value, after, next, final, receipt,
    force_structure formulas solver inventory actual ready known domain stored ranges memos valid⟩

private theorem leaf_structure (actual : Leaf record values path input before result after)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (inputDomain : DNode input) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result := by
  cases actual with
  | apply forced step =>
      obtain ⟨_, _, receipt, middleStored, targetDomain⟩ := force formulas solver inventory forced ready known domain
        stored coherent active member ranges memos valid
      cases step with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace receipt.ready.checked.good
            receipt.ready.checked.semantic middleStored.native ⟨rfl, targetDomain, inputDomain⟩
          exact ⟨advance_stored _ _ middleStored checked.1, checked.2.1, checked.2.2.2⟩

/-- The same actual leaf receipt bounds height by its current input and retains structural tables. -/
theorem leaf (actual : Leaf record values path input before result after)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input)
    (inputDomain : DNode input) (ranges : LeafRanges record values path input before)
    (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    ∃ next final, LeafReceipt formulas solver next record values base path input before result after memos final ∧
      Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result := by
  have closed := SourceCurrentAllocatedFiniteOrdinaryFinite.closed _
    ready.checked.semantic.ready.semantic.1.normal.facts.coherent input available inputDomain
  obtain ⟨next, final, receipt⟩ := actual.verified formulas solver inventory ready known
    (selected_domains formulas solver inventory ready known domain) coherent active member available closed ranges memos valid
  exact ⟨next, final, receipt,
    leaf_structure formulas solver inventory actual ready known domain stored coherent active member inputDomain ranges.1 memos valid⟩

/-- Initial domains and reached checks construct an actual leaf with its full receipt and height bound. -/
theorem leaf_finite (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input)
    (inputDomain : DNode input) (ranges : LeafRanges record values path input before)
    (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    ∃ result after next final, LeafReceipt formulas solver next record values base path input before result after memos final ∧
      Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result := by
  have closed := SourceCurrentAllocatedFiniteOrdinaryFinite.closed _
    ready.checked.semantic.ready.semantic.1.normal.facts.coherent input available inputDomain
  obtain ⟨result, after, next, final, receipt⟩ := SourceCurrentAllocatedSharedTargetLeaf.complete
    formulas solver inventory record values base before ready known (selected_domains formulas solver inventory ready known domain)
    coherent active path member input available closed ranges memos valid
  exact ⟨result, after, next, final, receipt,
    leaf_structure formulas solver inventory receipt.actual ready known domain stored coherent active member inputDomain ranges.1 memos valid⟩
end Producers
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryShared
