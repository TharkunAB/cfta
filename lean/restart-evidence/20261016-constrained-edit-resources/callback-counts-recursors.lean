import MicroCFTA.SourceCurrentAllocatedSharedEditGraph
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryValuePositions

/-!
# Callback counts on exact current edit graphs

Each node leaf makes one shared Leaf call. Counts retain the actual graph,
its input records, and all physical states. Empty below-edits and ignored
list-root leaves make no call. The bounds use original input positions.
No callback law, range plan, or capacity premise is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open Cache InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Positions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.node
local notation "RowPositions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.rows
local notation "ChildPositions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.children
local notation "EdgeCount" => SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

mutual
/-- Count shared Leaf calls in this exact node edit. -/
inductive NodeCount {record originals} :
    {edits : Edits EqualityNormalize.Path} → {value : Value Symbol Guard} → {before : SharedState width} →
    {result : Value Symbol Guard} → {after : SharedState width} →
    EditNode record originals edits value before result after → Nat → Prop where
  | leaf (actual : Leaf record originals target value before result after) : NodeCount (.leaf actual) 1
  | empty : NodeCount (.empty (record := record) (originals := originals) (entries := entries) (state := state)) 0
  | ordinary {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)}
      (counted : RowsCount actual calls) :
      NodeCount (.ordinary (entry := entry) (depth := depth) (free := free) actual built) calls
  | recursive {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      (counted : NodeCount body calls) : NodeCount (.recursive recursive head body) calls

/-- Count selected children in their actual source order. -/
inductive ChildrenCount {record originals} :
    {entries : List (Int × Edits EqualityNormalize.Path)} → {offset : Nat} → {values : List (Value Symbol Guard)} →
    {before : SharedState width} → {results : List (Value Symbol Guard)} → {after : SharedState width} →
    EditChildren record originals entries offset values before results after → Nat → Prop where
  | nil : ChildrenCount (.nil (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) 0
  | unselected {offset : Nat} {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after}
      (counted : ChildrenCount rest calls) : ChildrenCount (.unselected (value := value) offset absent rest) calls
  | selected {offset : Nat} {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after}
      (head : NodeCount first firstCalls) (tail : ChildrenCount rest restCalls) :
      ChildrenCount (.selected offset found first rest) (firstCalls + restCalls)

/-- Add each original row's child calls and its later-row calls. -/
inductive RowsCount {record originals} :
    {entries : List (Int × Edits EqualityNormalize.Path)} → {edges : List (EdgeValue Symbol Guard)} →
    {before : SharedState width} → {results : List (EdgeValue Symbol Guard)} → {after : SharedState width} →
    EditRows record originals entries edges before results after → Nat → Prop where
  | nil : RowsCount (.nil (record := record) (originals := originals) (entries := entries) (state := state)) 0
  | cons {edge : EdgeValue Symbol Guard} {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
      (head : ChildrenCount children firstCalls) (tail : RowsCount rest restCalls) :
      RowsCount (.cons children rebuilt rest) (firstCalls + restCalls)
end

/-- A list-root leaf is ignored; a below-edit uses its exact child count. -/
inductive ListCount {record originals} :
    {edits : Edits EqualityNormalize.Path} → {values : List (Value Symbol Guard)} → {before : SharedState width} →
    {results : List (Value Symbol Guard)} → {after : SharedState width} →
    EditList record originals edits values before results after → Nat → Prop where
  | leaf : ListCount (.leaf (record := record) (originals := originals) (target := target) (values := values) (state := state)) 0
  | children {actual : EditChildren record originals entries 0 values before results after}
      (counted : ChildrenCount actual calls) : ListCount (.children actual) calls


#check @EditNode.rec
#check @ChildrenCount.rec
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
