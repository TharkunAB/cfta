import MicroCFTA.SourceEqualitySharedEditGraph

/-!
# Actual-prefix checks for simultaneous edits with shared targets

First force checks use the actual target demand graph. Native leaf checks
use its returned state. Later rows use only completed source prefixes.
The precondition supplies no completed target, leaf, or edit execution.
-/
namespace MicroCFTA.SourceEqualitySharedEditRanges
open InternedConstructorTemplates SourceEqualityEdits SourceEqualitySharedTargetState SourceEqualitySharedEditGraph

mutual
  /-- Request word checks along the actual source node branches. -/
  inductive NodeRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Prop where
    | leaf (ranges : SourceEqualitySharedTargetLeafComplete.LeafRanges emptyGuard conjoin clear top record originals target value before) :
        NodeRanges emptyGuard conjoin clear top record originals (.editAt target) value before
    | empty : NodeRanges emptyGuard conjoin clear top record originals (.editBelow entries) .empty state
    | ordinary (rows : RowsRanges emptyGuard conjoin clear top record originals entries edges before) :
        NodeRanges emptyGuard conjoin clear top record originals (.editBelow entries) (.node entry edges depth free) before
    | recursive (recursive : SourceEqualityRequiredGraph.Recursive original)
        (body : ∀ exposed heap, SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
          NodeRanges emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap)) :
        NodeRanges emptyGuard conjoin clear top record originals (.editBelow entries) original before

  /-- Later child checks use the actual completed first edit's full native state. -/
  inductive ChildrenRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → Nat → List (Value Symbol Guard) → SharedState width Symbol Guard → Prop where
    | nil : ChildrenRanges emptyGuard conjoin clear top record originals entries index [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : ChildrenRanges emptyGuard conjoin clear top record originals entries (index + 1) values before) :
        ChildrenRanges emptyGuard conjoin clear top record originals entries index (value :: values) before
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : NodeRanges emptyGuard conjoin clear top record originals edits value before)
        (rest : ∀ result middle, EditNode emptyGuard conjoin clear top record originals edits value before result middle →
          ChildrenRanges emptyGuard conjoin clear top record originals entries (index + 1) values middle) :
        ChildrenRanges emptyGuard conjoin clear top record originals entries index (value :: values) before

  /-- Later row checks use actual child results and the subsequent literal edge request. -/
  inductive RowsRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → List (EdgeValue Symbol Guard) → SharedState width Symbol Guard → Prop where
    | nil : RowsRanges emptyGuard conjoin clear top record originals entries [] state
    | cons (children : ChildrenRanges emptyGuard conjoin clear top record originals entries 0 edge.children before)
        (rest : ∀ values middle, EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
          RowsRanges emptyGuard conjoin clear top record originals entries edges (advanceHeap middle
            (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2)) :
        RowsRanges emptyGuard conjoin clear top record originals entries (edge :: edges) before
end

/-- A source child-list root callback is ignored and requires no native word check. -/
def ListRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (edits : Edits EqualityNormalize.Path)
    (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenRanges emptyGuard conjoin clear top record originals entries 0 values before

end MicroCFTA.SourceEqualitySharedEditRanges
