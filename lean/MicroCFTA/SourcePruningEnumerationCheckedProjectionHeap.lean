import MicroCFTA.SourcePruningEnumerationCheckedProjection

/-!
# Projection heaps through the actual checked edge constructor

The accepted branch emits its checked original guard.
The rejected branch emits the Top sentinel guard.
Equality allocation changes no native edge record before this constructor.
-/
namespace MicroCFTA.SourcePruningEnumerationCheckedProjectionHeap
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Both actual checked constructor branches preserve the whole physical heap property. -/
theorem work_heap (symbol : Symbol) (constraint : Constraint)
    (children : List (Value Symbol Constraint)) (before : State Symbol Constraint)
    (heap : SourceEqualityAnnotationHeap.Heap projectable before) :
    SourceEqualityAnnotationHeap.Heap projectable
      (run (SourceEqualityMkEdgeAllocation.work symbol constraint children
        (SourceEqualityMkEdgeAllocation.accepted constraint children.length)) before).2 := by
  cases selected : SourceEqualityMkEdgeAllocation.accepted constraint children.length with
  | false =>
      have sentinel : projectable top := by
        change (some ([], none) : Option (List EqualityTrie.Trie × Option Constraint)) ≠ none
        intro impossible
        cases impossible
      simpa only [SourceEqualityMkEdgeAllocation.work, selected, Bool.false_eq_true, ↓reduceIte] using
        SourceEqualityAnnotationHeap.run projectable (makeEdge symbol top [.empty])
          (SourceEqualityAnnotationHeap.makeEdge projectable symbol top [.empty] sentinel) before heap
  | true =>
      have original := SourcePruningEnumerationCheckedProjection.accepted_projectable
        constraint children.length selected
      simpa only [SourceEqualityMkEdgeAllocation.work, selected, ↓reduceIte] using
        SourceEqualityAnnotationHeap.run projectable (makeEdge symbol constraint children)
          (SourceEqualityAnnotationHeap.makeEdge projectable symbol constraint children original) before heap

/-- Actual equality checks determine the selected work without a supplied successful result. -/
theorem build_heap (symbol : Symbol) (stored : SourceEqualityConstraintAllocation.Value)
    (guard : SourceGuards.Guard FullSyntax.Formula)
    (children : List (Value Symbol Constraint))
    (operations : SourceEqualityConstraintMemoAllocation.State) (before : State Symbol Constraint)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (ready : SourceEqualityConstraintAllocation.Ready operations.constraints stored)
    (heap : SourceEqualityAnnotationHeap.Heap projectable before) :
    SourceEqualityAnnotationHeap.Heap projectable
      (SourceEqualityMkEdgeAllocation.build symbol stored guard children operations before).2.2 := by
  have actual := SourceEqualityMkEdgeAllocation.build_receipt symbol stored guard children
    operations before valid ready
  rw [actual.1]
  exact work_heap symbol (SourceEqualityAccessorAllocation.constraint stored guard) children before heap

end MicroCFTA.SourcePruningEnumerationCheckedProjectionHeap

namespace MicroCFTA.SourceCurrentAllocatedMkEdge
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

/-- A concrete checked allocated constructor preserves the original heap property. -/
theorem build_projectable_heap (symbol : Symbol) (constraint : Allocated)
    (children : List (Value Symbol Constraint)) (before : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (ready : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (heap : SourceEqualityAnnotationHeap.Heap projectable before.native.machine.heap) :
    SourceEqualityAnnotationHeap.Heap projectable
      (build symbol constraint children before).2.native.machine.heap := by
  change SourceEqualityAnnotationHeap.Heap projectable
    (SourceEqualityMkEdgeAllocation.build symbol constraint.stored constraint.guard children
      before.operations before.native.machine.heap).2.2
  exact SourcePruningEnumerationCheckedProjectionHeap.build_heap symbol constraint.stored
    constraint.guard children before.operations before.native.machine.heap valid ready heap

/-- A retained actual checked receipt identifies the same returned physical heap. -/
theorem Receipt.preserves_projection_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Constraint)}
    {before after : SourceEqualityNativeDemand.State width} {result : EdgeValue Symbol Constraint}
    (receipt : Receipt formulas solver inventory symbol constraint children before result after)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (ready : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (heap : SourceEqualityAnnotationHeap.Heap projectable before.native.machine.heap) :
    SourceEqualityAnnotationHeap.Heap projectable after.native.machine.heap := by
  have same : (build symbol constraint children before).2 = after := congrArg Prod.snd receipt.actual
  rw [← same]
  exact build_projectable_heap symbol constraint children before valid ready heap

/-- The concrete contradiction sentinel preserves the whole original projection heap. -/
theorem reject_projectable_heap (symbol : Symbol) (before : SourceEqualityNativeDemand.State width)
    (heap : SourceEqualityAnnotationHeap.Heap projectable before.native.machine.heap) :
    SourceEqualityAnnotationHeap.Heap projectable (reject symbol before).2.native.machine.heap := by
  have sentinel : projectable top := by
    change (some ([], none) : Option (List EqualityTrie.Trie × Option Constraint)) ≠ none
    intro impossible
    cases impossible
  exact SourceEqualityAnnotationHeap.run projectable (makeEdge symbol top [.empty])
    (SourceEqualityAnnotationHeap.makeEdge projectable symbol top [.empty] sentinel)
    before.native.machine.heap heap

end MicroCFTA.SourceCurrentAllocatedMkEdge
