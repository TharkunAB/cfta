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

mutual
/-- Every finite actual node graph has its own exact callback count. -/
theorem node_count {record originals edits value before result after}
    (actual : EditNode (width := width) record originals edits value before result after) :
    ∃ calls, NodeCount actual calls := by
  cases actual with
  | leaf actual => exact ⟨1, .leaf actual⟩
  | empty => exact ⟨0, .empty⟩
  | ordinary rows built =>
      obtain ⟨calls, counted⟩ := rows_count rows
      exact ⟨calls, .ordinary counted⟩
  | recursive recursive head body =>
      obtain ⟨calls, counted⟩ := node_count body
      exact ⟨calls, .recursive counted⟩
termination_by structural actual

/-- Every finite actual child graph retains the sum of its selected calls. -/
theorem children_count {record originals entries offset values before results after}
    (actual : EditChildren (width := width) record originals entries offset values before results after) :
    ∃ calls, ChildrenCount actual calls := by
  cases actual with
  | nil => exact ⟨0, .nil⟩
  | unselected offset absent rest =>
      obtain ⟨calls, counted⟩ := children_count rest
      exact ⟨calls, .unselected counted⟩
  | selected offset found first rest =>
      obtain ⟨firstCalls, head⟩ := node_count first
      obtain ⟨restCalls, tail⟩ := children_count rest
      exact ⟨firstCalls + restCalls, .selected head tail⟩
termination_by structural actual

/-- Every finite actual row graph retains all repeated row occurrences. -/
theorem rows_count {record originals entries edges before results after}
    (actual : EditRows (width := width) record originals entries edges before results after) :
    ∃ calls, RowsCount actual calls := by
  cases actual with
  | nil => exact ⟨0, .nil⟩
  | cons children built rest =>
      obtain ⟨firstCalls, head⟩ := children_count children
      obtain ⟨restCalls, tail⟩ := rows_count rest
      exact ⟨firstCalls + restCalls, .cons head tail⟩
termination_by structural actual
end

/-- Every finite actual list graph has its exact ignored-leaf or child count. -/
theorem list_count {record originals edits values before results after}
    (actual : EditList (width := width) record originals edits values before results after) :
    ∃ calls, ListCount actual calls := by
  cases actual with
  | leaf => exact ⟨0, .leaf⟩
  | children actual =>
      obtain ⟨calls, counted⟩ := children_count actual
      exact ⟨calls, .children counted⟩

mutual
/-- Finite ordinary node callbacks fit the original input's literal positions. -/
theorem NodeCount.bound {record originals edits value before result after calls}
    {actual : EditNode (width := width) record originals edits value before result after}
    (counted : NodeCount actual calls) (domain : DNode value) : calls ≤ Positions value := by
  cases counted with
  | leaf => exact SourceCurrentAllocatedFiniteOrdinaryValuePositions.node_pos _
  | empty => exact Nat.zero_le _
  | ordinary counted =>
      have bound := RowsCount.bound counted domain.rows
      exact Nat.le_trans bound (Nat.le_add_left _ _)
  | @recursive _ _ _ _ _ _ _ recursive _ _ _ _ => cases domain <;> cases recursive
termination_by structural counted

/-- Ordered child callbacks fit the original forest, including Empty roots. -/
theorem ChildrenCount.bound {record originals entries offset values before results after calls}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (counted : ChildrenCount actual calls) (domain : DChildren values) : calls ≤ ChildPositions values := by
  cases counted with
  | nil => exact Nat.zero_le _
  | unselected counted =>
      cases domain with
      | cons _ rest => exact Nat.le_trans (ChildrenCount.bound counted rest) (Nat.le_add_left _ _)
  | selected head tail =>
      cases domain with
      | cons first rest => exact Nat.add_le_add (NodeCount.bound head first) (ChildrenCount.bound tail rest)
termination_by structural counted

/-- Ordered row callbacks fit all original row child positions. -/
theorem RowsCount.bound {record originals entries edges before results after calls}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (counted : RowsCount actual calls) (domain : DRows edges) : calls ≤ RowPositions edges := by
  cases counted with
  | nil => exact Nat.zero_le _
  | cons head tail =>
      cases domain with
      | cons first rest => exact Nat.add_le_add (ChildrenCount.bound head first) (RowsCount.bound tail rest)
termination_by structural counted
end

/-- The ignored list-root callback contributes zero; other lists use their children. -/
theorem ListCount.bound {record originals edits values before results after calls}
    {actual : EditList (width := width) record originals edits values before results after}
    (counted : ListCount actual calls) (domain : DChildren values) : calls ≤ ChildPositions values := by
  cases counted with
  | leaf => exact Nat.zero_le _
  | children counted => exact ChildrenCount.bound counted domain

/-- Actual node counts inherit the input-only profile and height envelope. -/
theorem NodeCount.profile {record originals edits value before result after calls}
    {actual : EditNode (width := width) record originals edits value before result after}
    (counted : NodeCount actual calls) (rows arity bound : Nat)
    (profile : NodeShape rows arity value) (heightBound : height value ≤ bound) :
    calls ≤ 1 + arity * EdgeCount rows arity bound :=
  Nat.le_trans (counted.bound (NodeShape.domain value profile))
    (SourceCurrentAllocatedFiniteOrdinaryValuePositions.profile_node value profile bound heightBound)

/-- Actual list counts inherit the input-only forest profile and length envelope. -/
theorem ListCount.profile {record originals edits values before results after calls}
    {actual : EditList (width := width) record originals edits values before results after}
    (counted : ListCount actual calls) (rows arity count bound : Nat)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count)
    (heightBound : childrenHeight values ≤ bound) :
    calls ≤ count * (1 + arity * EdgeCount rows arity bound) :=
  Nat.le_trans (counted.bound (ChildrenShape.domain values profile))
    (SourceCurrentAllocatedFiniteOrdinaryValuePositions.profile_forest values profile count bound lengthBound heightBound)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
