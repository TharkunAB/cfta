import MicroCFTA.SourceCurrentMemoSharedTargetLeaf
import MicroCFTA.SourceEqualityEdits
import MicroCFTA.SourceEqualityRequiredGraph

/-!
# Simultaneous native edits with memo-aware shared targets

Leaf tokens identify original class paths. First use constructs their target
from the captured original forest. Later uses retain that physical value.
Every traversal retains the slots, full native state, and completed merge table.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditGraph
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityRequiredHead
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetLeaf

/-- The edit state retains actual native state and all returned class target closure slots. -/
abbrev SharedState (width : Nat) (Symbol Guard : Type) := SourceCurrentMemoSharedTargetState.State width Symbol Guard

mutual
  /-- One source node edit with a physical native intersection at each leaf. -/
  inductive EditNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard →
        Value Symbol Guard → SharedState width Symbol Guard → Prop where
    | leaf (actual : Leaf emptyGuard conjoin clear top record originals target value before result after) :
        EditNode emptyGuard conjoin clear top record originals (.editAt target) value before result after
    | empty : EditNode emptyGuard conjoin clear top record originals (.editBelow entries) .empty state .empty state
    | ordinary (rows : EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle)
        (built : run (makeNode rebuilt) middle.native.machine.heap = (value, heap)) :
        EditNode emptyGuard conjoin clear top record originals (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap)
    | recursive (recursive : SourceEqualityRequiredGraph.Recursive original)
        (head : Head original before.native.machine.heap exposed heap)
        (body : EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) value after) :
        EditNode emptyGuard conjoin clear top record originals (.editBelow entries) original before value after

  /-- Ordered child scans retain actual warm states between selected edit subtrees. -/
  inductive EditChildren [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → Nat → List (Value Symbol Guard) → SharedState width Symbol Guard →
        List (Value Symbol Guard) → SharedState width Symbol Guard → Prop where
    | nil : EditChildren emptyGuard conjoin clear top record originals entries index [] state [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values before results after) :
        EditChildren emptyGuard conjoin clear top record originals entries index (value :: values) before (value :: results) after
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : EditNode emptyGuard conjoin clear top record originals edits value before result middle)
        (rest : EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values middle results after) :
        EditChildren emptyGuard conjoin clear top record originals entries index (value :: values) before (result :: results) after

  /-- All original rows are rebuilt with full guards and the actual constructor cache. -/
  inductive EditRows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → List (EdgeValue Symbol Guard) → SharedState width Symbol Guard →
        List (EdgeValue Symbol Guard) → SharedState width Symbol Guard → Prop where
    | nil : EditRows emptyGuard conjoin clear top record originals entries [] state [] state
    | cons (children : EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle)
        (rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap))
        (rest : EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after) :
        EditRows emptyGuard conjoin clear top record originals entries (edge :: edges) before (result :: results) after
end

/-- Source child-list leaves are ignored; below-edits execute the stored signed map. -/
inductive EditList [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
    Edits EqualityNormalize.Path → List (Value Symbol Guard) → SharedState width Symbol Guard →
      List (Value Symbol Guard) → SharedState width Symbol Guard → Prop where
  | leaf : EditList emptyGuard conjoin clear top record originals (.editAt target) values state values state
  | children (trace : EditChildren emptyGuard conjoin clear top record originals entries 0 values before results after) :
      EditList emptyGuard conjoin clear top record originals (.editBelow entries) values before results after

end MicroCFTA.SourceCurrentMemoSharedEditGraph
