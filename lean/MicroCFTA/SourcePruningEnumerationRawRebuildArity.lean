import MicroCFTA.SourceCurrentAllocatedRawRebuild
import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Arity through actual raw reconstruction

An equal-arity edge replacement copies the original resident guard.
Coherence connects its actual child count to its canonical key.
Node reconstruction adds no edge record.
-/
namespace MicroCFTA.SourcePruningEnumerationRawRebuildArity
open InternedConstructorTemplates
open SourcePruningEnumerationArityOrigins (Fits Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual equal-arity raw edge rebuild retains every old and newly interned key's arity. -/
theorem edge_heap (original : Edge) (children : List Node) (before : Checked width)
    (heap : Heap before.native.machine.heap)
    (coherent : InternedRecordCoherence.Coherent before.native.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap original)
    (same : children.length = original.children.length) :
    Heap (SourceCurrentAllocatedRawRebuild.edge original children before).2.native.machine.heap := by
  have checked : Fits original.entry.key.constraint children.length := by
    rw [same]
    exact heap.edge _ coherent original resident
  change Heap (run (makeEdge original.entry.key.symbol original.entry.key.constraint children)
    before.native.machine.heap).2
  exact SourcePruningEnumerationArityOrigins.edge_heap original.entry.key.symbol original.entry.key.constraint
    children before.native.machine.heap heap checked

/-- Both actual modifyNode branches retain arity without a new per-row condition. -/
theorem modify_heap (original : Node) (oldRows newRows : List Edge) (before : Checked width)
    (heap : Heap before.native.machine.heap) :
    Heap (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).2.native.machine.heap := by
  unfold SourceCurrentAllocatedRawRebuild.modify SourceEqualityPartialNodeRebuild.modify
  split
  · exact heap
  · exact SourcePruningEnumerationArityOrigins.node_heap newRows before.native.machine.heap heap

end MicroCFTA.SourcePruningEnumerationRawRebuildArity
