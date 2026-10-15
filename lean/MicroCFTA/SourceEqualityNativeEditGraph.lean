import MicroCFTA.SourceEqualityEdits
import MicroCFTA.SourceEqualityNativeScoped
import MicroCFTA.SourceEqualityRequiredGraph

/-!
# Simultaneous native edits with captured physical targets

Leaves execute actual checked native intersection requests. Every constructor
operation advances the same full native state. The graph retains source
branch priority, signed child selection, and all original row guards.
-/
namespace MicroCFTA.SourceEqualityNativeEditGraph
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityRequiredHead SourceEqualityNativeScoped

/-- The full source state includes constructor, domain, and both native memo caches. -/
abbrev NativeState (width : Nat) (Symbol Guard : Type) := SourceRecursiveIntersectionThunks.State width Symbol Guard

mutual
  /-- One source node edit with a physical native intersection at each leaf. -/
  inductive EditNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
      Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard →
        Value Symbol Guard → NativeState width Symbol Guard → Prop where
    | leaf (actual : Step emptyGuard conjoin target value before result after) :
        EditNode emptyGuard conjoin (.editAt target) value before result after
    | empty : EditNode emptyGuard conjoin (.editBelow entries) .empty state .empty state
    | ordinary (rows : EditRows emptyGuard conjoin entries edges before rebuilt middle)
        (built : run (makeNode rebuilt) middle.machine.heap = (value, heap)) :
        EditNode emptyGuard conjoin (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap)
    | recursive (recursive : SourceEqualityRequiredGraph.Recursive original)
        (head : Head original before.machine.heap exposed heap)
        (body : EditNode emptyGuard conjoin (.editBelow entries) exposed (advanceHeap before heap) value after) :
        EditNode emptyGuard conjoin (.editBelow entries) original before value after

  /-- Ordered child scans retain actual warm states between selected edit subtrees. -/
  inductive EditChildren [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
      List (Int × Edits (Value Symbol Guard)) → Nat → List (Value Symbol Guard) → NativeState width Symbol Guard →
        List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
    | nil : EditChildren emptyGuard conjoin entries index [] state [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : EditChildren emptyGuard conjoin entries (index + 1) values before results after) :
        EditChildren emptyGuard conjoin entries index (value :: values) before (value :: results) after
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : EditNode emptyGuard conjoin edits value before result middle)
        (rest : EditChildren emptyGuard conjoin entries (index + 1) values middle results after) :
        EditChildren emptyGuard conjoin entries index (value :: values) before (result :: results) after

  /-- All original rows are rebuilt with full guards and the actual constructor cache. -/
  inductive EditRows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
      List (Int × Edits (Value Symbol Guard)) → List (EdgeValue Symbol Guard) → NativeState width Symbol Guard →
        List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Prop where
    | nil : EditRows emptyGuard conjoin entries [] state [] state
    | cons (children : EditChildren emptyGuard conjoin entries 0 edge.children before values middle)
        (rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap = (result, heap))
        (rest : EditRows emptyGuard conjoin entries edges (advanceHeap middle heap) results after) :
        EditRows emptyGuard conjoin entries (edge :: edges) before (result :: results) after
end

/-- Source child-list leaves are ignored; below-edits execute the stored signed map. -/
inductive EditList [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Edits (Value Symbol Guard) → List (Value Symbol Guard) → NativeState width Symbol Guard →
      List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | leaf : EditList emptyGuard conjoin (.editAt target) values state values state
  | children (trace : EditChildren emptyGuard conjoin entries 0 values before results after) :
      EditList emptyGuard conjoin (.editBelow entries) values before results after

end MicroCFTA.SourceEqualityNativeEditGraph
