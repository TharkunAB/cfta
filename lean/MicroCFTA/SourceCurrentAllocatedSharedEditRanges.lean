import MicroCFTA.SourceCurrentAllocatedSharedEditGraph

/-!
# Actual-prefix checks for simultaneous edits with shared targets

First force checks use the actual target demand graph. Native leaf checks
use its returned state. Later rows use only completed source prefixes.
The precondition supplies no completed target, leaf, or edit execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditRanges
open InternedConstructorTemplates SourceEqualityEdits SourceCurrentAllocatedSharedEditGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

mutual
  /-- Request word checks along the actual source node branches. -/
  inductive NodeRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width → Prop where
    | leaf (ranges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals target value before) :
        NodeRanges record originals (.editAt target) value before
    | empty : NodeRanges record originals (.editBelow entries) .empty state
    | ordinary (rows : RowsRanges record originals entries edges before) :
        NodeRanges record originals (.editBelow entries) (.node entry edges depth free) before
    | recursive (recursive : SourceEqualityRequiredGraph.Recursive original)
        (body : ∀ exposed heap, SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap →
          NodeRanges record originals (.editBelow entries) exposed (advanceHeap before heap)) :
        NodeRanges record originals (.editBelow entries) original before

  /-- Later child checks use the actual completed first edit's full native state. -/
  inductive ChildrenRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → Nat → List (Value Symbol Guard) → SharedState width → Prop where
    | nil : ChildrenRanges record originals entries index [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : ChildrenRanges record originals entries (index + 1) values before) :
        ChildrenRanges record originals entries index (value :: values) before
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : NodeRanges record originals edits value before)
        (rest : ∀ result middle, EditNode record originals edits value before result middle →
          ChildrenRanges record originals entries (index + 1) values middle) :
        ChildrenRanges record originals entries index (value :: values) before

  /-- Later row checks use actual child results and the subsequent literal edge request. -/
  inductive RowsRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → List (EdgeValue Symbol Guard) → SharedState width → Prop where
    | nil : RowsRanges record originals entries [] state
    | cons (children : ChildrenRanges record originals entries 0 edge.children before)
        (rest : ∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
          RowsRanges record originals entries edges (advanceHeap middle
            (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) :
        RowsRanges record originals entries (edge :: edges) before
end

/-- A source child-list root callback is ignored and requires no native word check. -/
def ListRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (edits : Edits EqualityNormalize.Path)
    (values : List (Value Symbol Guard)) (before : SharedState width) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenRanges record originals entries 0 values before

end MicroCFTA.SourceCurrentAllocatedSharedEditRanges
