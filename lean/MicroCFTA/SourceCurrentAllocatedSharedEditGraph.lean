import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
import MicroCFTA.SourceCurrentRequiredQueryMemos
import MicroCFTA.SourceEqualityEdits
import MicroCFTA.SourceEqualityRequiredGraph

/-!
# Simultaneous edits with the current checked native state

Leaf tokens identify original class paths. First use constructs their target
from the captured original forest. Later uses retain that physical value.
Every traversal retains the slots, full checked state, and completed merge table.
Same-arity row reconstruction uses the original raw guard.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditGraph
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityRequiredHead
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf

/-- The edit state retains actual native state and all returned class target closure slots. -/
abbrev SharedState (width : Nat) := SourceCurrentAllocatedSharedTargetState.State width

/-- Constructor-only work retains operations, native tables, target slots, and the merge table. -/
def advanceHeap (before : SharedState width) (heap : Heap) : SharedState width :=
  SourceCurrentAllocatedSharedTargetState.advance before
    (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)

mutual
  /-- One source node edit with a physical native intersection at each leaf. -/
  inductive EditNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width →
        Value Symbol Guard → SharedState width → Prop where
    | leaf (actual : Leaf record originals target value before result after) :
        EditNode record originals (.editAt target) value before result after
    | empty : EditNode record originals (.editBelow entries) .empty state .empty state
    | ordinary (rows : EditRows record originals entries edges before rebuilt middle)
        (built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)) :
        EditNode record originals (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap)
    | recursive (recursive : SourceEqualityRequiredGraph.Recursive original)
        (head : Head original before.checked.native.machine.heap exposed heap)
        (body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after) :
        EditNode record originals (.editBelow entries) original before value after

  /-- Ordered child scans retain actual warm states between selected edit subtrees. -/
  inductive EditChildren [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → Nat → List (Value Symbol Guard) → SharedState width →
        List (Value Symbol Guard) → SharedState width → Prop where
    | nil : EditChildren record originals entries index [] state [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : EditChildren record originals entries (index + 1) values before results after) :
        EditChildren record originals entries index (value :: values) before (value :: results) after
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : EditNode record originals edits value before result middle)
        (rest : EditChildren record originals entries (index + 1) values middle results after) :
        EditChildren record originals entries index (value :: values) before (result :: results) after

  /-- All original rows are rebuilt with full guards and the actual constructor cache. -/
  inductive EditRows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → List (EdgeValue Symbol Guard) → SharedState width →
        List (EdgeValue Symbol Guard) → SharedState width → Prop where
    | nil : EditRows record originals entries [] state [] state
    | cons (children : EditChildren record originals entries 0 edge.children before values middle)
        (rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap))
        (rest : EditRows record originals entries edges (advanceHeap middle heap) results after) :
        EditRows record originals entries (edge :: edges) before (result :: results) after
end

/-- Source child-list leaves are ignored; below-edits execute the stored signed map. -/
inductive EditList [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
    Edits EqualityNormalize.Path → List (Value Symbol Guard) → SharedState width →
      List (Value Symbol Guard) → SharedState width → Prop where
  | leaf : EditList record originals (.editAt target) values state values state
  | children (trace : EditChildren record originals entries 0 values before results after) :
      EditList record originals (.editBelow entries) values before results after

/-- Positional edits preserve arity, so source setChildren uses raw interning. -/
theorem children_length [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {record originals entries index values before results after}
    (actual : EditChildren (width := width) record originals entries index values before results after) :
    results.length = values.length := by
  exact EditChildren.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ values _ results _ _ => results.length = values.length)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    (by intros; rfl) (by intros; simp_all)
    (by intros; simp_all) (by intros; trivial)
    (by intros; trivial) actual

mutual
  /-- Node reads retain the actual leaf receipt and recursive head events. -/
  inductive NodeReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
      (base : Heap) :
      {record : SourceEqualityClassOrder.Record} → {originals : List (Value Symbol Guard)} →
      {edits : Edits EqualityNormalize.Path} → {value : Value Symbol Guard} → {before : SharedState width} →
      {result : Value Symbol Guard} → {after : SharedState width} →
      EditNode record originals edits value before result after → Memos → Memos → Prop where
    | leaf (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path
        value before result after memos saved) :
        NodeReads formulas solver base (.leaf receipt.actual) memos saved
    | empty : NodeReads formulas solver base .empty memos memos
    | ordinary {entries edges before rebuilt middle value heap entry depth free}
        {actual : EditRows record originals entries edges before rebuilt middle}
        {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)}
        (read : RowsReads formulas solver base actual memos saved) :
        NodeReads formulas solver base
          (.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos saved
    | recursive {entries original before exposed heap value after}
        {recursive : SourceEqualityRequiredGraph.Recursive original}
        {head : Head original before.checked.native.machine.heap exposed heap}
        {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
        (headRead : SourceCurrentRequiredQueryMemos.HeadReads head memos middle)
        (headGlobal : SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos middle)
        (bodyRead : NodeReads formulas solver base body middle saved) :
        NodeReads formulas solver base (.recursive recursive head body) memos saved

  /-- Selected children pass their returned global bundle to the next position. -/
  inductive ChildrenReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
      (base : Heap) :
      {record : SourceEqualityClassOrder.Record} → {originals : List (Value Symbol Guard)} →
      {entries : List (Int × Edits EqualityNormalize.Path)} → {offset : Nat} → {values : List (Value Symbol Guard)} →
      {before : SharedState width} → {results : List (Value Symbol Guard)} → {after : SharedState width} →
      EditChildren record originals entries offset values before results after → Memos → Memos → Prop where
    | nil : ChildrenReads formulas solver base .nil memos memos
    | unselected {entries values before results after value} {offset : Nat}
        {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
        {rest : EditChildren record originals entries (offset + 1) values before results after}
        (read : ChildrenReads formulas solver base rest memos saved) :
        ChildrenReads formulas solver base (.unselected (value := value) offset absent rest) memos saved
    | selected {entries edits value before result middle values results after} {offset : Nat}
        {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
        {first : EditNode record originals edits value before result middle}
        {rest : EditChildren record originals entries (offset + 1) values middle results after}
        (firstRead : NodeReads formulas solver base first memos current)
        (restRead : ChildrenReads formulas solver base rest current saved) :
        ChildrenReads formulas solver base (.selected offset found first rest) memos saved

  /-- Rows retain exact child, raw edge constructor, and later-row states. -/
  inductive RowsReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
      (base : Heap) :
      {record : SourceEqualityClassOrder.Record} → {originals : List (Value Symbol Guard)} →
      {entries : List (Int × Edits EqualityNormalize.Path)} → {edges : List (EdgeValue Symbol Guard)} →
      {before : SharedState width} → {results : List (EdgeValue Symbol Guard)} → {after : SharedState width} →
      EditRows record originals entries edges before results after → Memos → Memos → Prop where
    | nil : RowsReads formulas solver base .nil memos memos
    | cons {entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard}
        {children : EditChildren record originals entries 0 edge.children before values middle}
        {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
        {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
        (firstRead : ChildrenReads formulas solver base children memos current)
        (restRead : RowsReads formulas solver base rest current saved) :
        RowsReads formulas solver base (.cons children rebuilt rest) memos saved
end

/-- Child-list root callbacks are ignored and make no calls. -/
inductive ListReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (base : Heap) :
    {record : SourceEqualityClassOrder.Record} → {originals : List (Value Symbol Guard)} →
    {edits : Edits EqualityNormalize.Path} → {values : List (Value Symbol Guard)} → {before : SharedState width} →
    {results : List (Value Symbol Guard)} → {after : SharedState width} →
    EditList record originals edits values before results after → Memos → Memos → Prop where
  | leaf : ListReads formulas solver base .leaf memos memos
  | children (read : ChildrenReads formulas solver base actual memos saved) :
      ListReads formulas solver base (.children actual) memos saved

end MicroCFTA.SourceCurrentAllocatedSharedEditGraph


