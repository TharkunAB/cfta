import MicroCFTA.SourcePruningEnumerationMergeArity
import MicroCFTA.SourcePruningEnumerationProjectionArity
import MicroCFTA.SourcePruningEnumerationNativeQueryArity
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf

/-!
# Edge-record arity through actual shared targets and leaf queries

Actual operands retain their projection and allocated merge endpoints.
Each native query uses its recorded complete physical trace.
A shared hit changes no heap.
A shared miss follows the actual target reads before storing its slot.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetQuery
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual checked target query retains arity at its same complete native endpoint. -/
theorem Receipt.arity_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left right result : Value Symbol Guard}
    {before after : Checked width} {memos : Memos}
    (receipt : Receipt formulas solver inventory left right before result after memos)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases receipt.actual with
  | run trace =>
      exact SourcePruningEnumerationNativeQueryArity.node_query_heap
        ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ before after result _ good heap trace

end MicroCFTA.SourceCurrentAllocatedTargetQuery

namespace MicroCFTA.SourcePruningEnumerationSharedTargetArity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetComplete
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "SharedState" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual operand projects first and then merges at that same reached heap. -/
theorem operand_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {output : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo output after saved memos final)
    (ready : ClassReady before) (available : Values before.native.machine.heap values)
    (stored : Stored before.native.machine.heap memo) (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have middleHeap := SourcePruningEnumerationProjectionArity.forest_heap projection.graph
    ready.semantic ready.costs available heap
  cases merged.actual with
  | done actual =>
      exact SourcePruningEnumerationAllocatedMergeArity.call_heap actual
        (SourceCurrentAllocatedConjunctionMemo.ready middle projection.ready.good projection.ready.semantic projection.ready.costs)
        (stored.grows projection.effects.keeps) projection.available middleHeap

/-- Actual ordered target reads retain the same full reached states and stored merge table. -/
theorem fold_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedTargetGraph.Fold values seed paths before memo result after saved}
    (reads : FoldReads formulas solver actual memos final) (ready : ClassReady before)
    (available : Values before.native.machine.heap values) (stored : Stored before.native.machine.heap memo)
    (heap : Heap before.native.machine.heap) :
    ClassReady after ∧ Values after.native.machine.heap values ∧ Stored after.native.machine.heap saved ∧ Heap after.native.machine.heap := by
  induction reads with
  | nil receipt => exact ⟨receipt.ready, receipt.originals, receipt.stored, operand_heap receipt ready available stored heap⟩
  | cons receipt remaining query ih =>
      obtain ⟨laterReady, laterValues, laterStored, laterHeap⟩ := ih receipt.ready receipt.originals receipt.stored
        (operand_heap receipt ready available stored heap)
      exact ⟨query.ready, fun value member => query.effects.keeps.available value (laterValues value member),
        laterStored.grows query.effects.keeps, query.arity_heap laterReady.good laterHeap⟩

/-- Actual first-seeded target construction retains arity at its own returned checked heap. -/
theorem target_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedTargetGraph.Target values paths before memo result after saved}
    (reads : TargetReads formulas solver actual memos final) (ready : ClassReady before)
    (available : Values before.native.machine.heap values) (stored : Stored before.native.machine.heap memo)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases reads with
  | nil => exact heap
  | cons reads => exact (fold_heap reads ready available stored heap).2.2.2

/-- A real shared force reuses its slot or follows the same actual target miss reads. -/
theorem force_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : SharedState width} {result : Value Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedSharedTargetForce.Force record values path before result after}
    (reads : SourceCurrentAllocatedSharedTargetForce.Reads formulas solver actual memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (heap : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap := by
  cases reads with
  | hit => exact heap
  | miss _ reads =>
      exact target_heap reads ready.checked
        (fun value member => ready.captured.available value (known value member)) ready.stored heap

/-- The actual forced target precedes the recorded native leaf query at its returned heap. -/
theorem leaf_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path} {input result : Value Symbol Guard}
    {before after : SharedState width} {memos final : Memos}
    {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record values path input before result after}
    (reads : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (heap : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap := by
  cases reads with
  | apply first query =>
      have middleHeap := force_heap first.reads ready known heap
      exact query.arity_heap first.ready.checked.good middleHeap

end MicroCFTA.SourcePruningEnumerationSharedTargetArity

namespace MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "SharedState" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual full leaf receipt derives its edge-record arity from its genuine initial class state. -/
theorem Receipt.arity_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory initialInventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path} {input result : Value Symbol Guard}
    {before after : SharedState width} {memos final : Memos}
    (receipt : Receipt formulas solver inventory record values base path input before result after memos final)
    (ready : SharedReady formulas solver initialInventory record values base before) (known : Values base values)
    (heap : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap :=
  SourcePruningEnumerationSharedTargetArity.leaf_heap receipt.reads ready known heap

end MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
