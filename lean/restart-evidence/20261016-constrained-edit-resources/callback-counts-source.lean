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

private theorem counted {record originals} :
    (∀ {edits value before result after} (actual : EditNode (width := width) record originals edits value before result after),
      ∃ calls, NodeCount actual calls) ∧
    (∀ {entries offset values before results after} (actual : EditChildren (width := width) record originals entries offset values before results after),
      ∃ calls, ChildrenCount actual calls) ∧
    (∀ {entries edges before results after} (actual : EditRows (width := width) record originals entries edges before results after),
      ∃ calls, RowsCount actual calls) := by
  have leafCase : ∀ {target value} {before : SharedState width} {result} {after : SharedState width}
      (actual : Leaf record originals target value before result after),
      ∃ calls, NodeCount (.leaf actual) calls := fun actual => ⟨1, .leaf actual⟩
  have emptyCase : ∀ {entries state},
      ∃ calls, NodeCount (.empty (width := width) (record := record) (originals := originals) (entries := entries) (state := state)) calls :=
    ⟨0, .empty⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free}
      (actual : EditRows (width := width) record originals entries edges before rebuilt middle)
      (built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)),
      (∃ calls, RowsCount actual calls) →
        ∃ calls, NodeCount (.ordinary (entry := entry) (depth := depth) (free := free) actual built) calls := by
    intro entries edges before rebuilt middle value heap entry depth free actual built ih
    obtain ⟨calls, own⟩ := ih
    exact ⟨calls, .ordinary (built := built) own⟩
  have recursiveCase : ∀ {original exposed heap entries before value after}
      (recursive : SourceEqualityRequiredGraph.Recursive original)
      (head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap)
      (body : EditNode (width := width) record originals (.editBelow entries) exposed (advanceHeap before heap) value after),
      (∃ calls, NodeCount body calls) → ∃ calls, NodeCount (.recursive recursive head body) calls := by
    intro original exposed heap entries before value after recursive head body ih
    obtain ⟨calls, own⟩ := ih
    exact ⟨calls, .recursive (recursive := recursive) (head := head) own⟩
  have nilChildren : ∀ {entries offset state},
      ∃ calls, ChildrenCount (.nil (width := width) (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) calls :=
    ⟨0, .nil⟩
  have unselectedCase : ∀ {entries values before results after value} (offset : Nat)
      (absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none)
      (rest : EditChildren (width := width) record originals entries (offset + 1) values before results after),
      (∃ calls, ChildrenCount rest calls) → ∃ calls, ChildrenCount (.unselected (value := value) offset absent rest) calls := by
    intro entries values before results after value offset absent rest ih
    obtain ⟨calls, own⟩ := ih
    exact ⟨calls, .unselected (absent := absent) own⟩
  have selectedCase : ∀ {entries edits value before result middle values results after} (offset : Nat)
      (found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits)
      (first : EditNode (width := width) record originals edits value before result middle)
      (rest : EditChildren (width := width) record originals entries (offset + 1) values middle results after),
      (∃ calls, NodeCount first calls) → (∃ calls, ChildrenCount rest calls) →
        ∃ calls, ChildrenCount (.selected offset found first rest) calls := by
    intro entries edits value before result middle values results after offset found first rest firstIH restIH
    obtain ⟨firstCalls, head⟩ := firstIH
    obtain ⟨restCalls, tail⟩ := restIH
    exact ⟨firstCalls + restCalls, .selected (found := found) head tail⟩
  have nilRows : ∀ {entries state},
      ∃ calls, RowsCount (.nil (width := width) (record := record) (originals := originals) (entries := entries) (state := state)) calls :=
    ⟨0, .nil⟩
  have consCase : ∀ {entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard}
      (children : EditChildren (width := width) record originals entries 0 edge.children before values middle)
      (built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap))
      (rest : EditRows (width := width) record originals entries edges (advanceHeap middle heap) results after),
      (∃ calls, ChildrenCount children calls) → (∃ calls, RowsCount rest calls) →
        ∃ calls, RowsCount (.cons children built rest) calls := by
    intro entries before values middle result heap edges results after edge children built rest firstIH restIH
    obtain ⟨firstCalls, head⟩ := firstIH
    obtain ⟨restCalls, tail⟩ := restIH
    exact ⟨firstCalls + restCalls, .cons (rebuilt := built) head tail⟩
  constructor
  · intro edits value before result after actual
    exact EditNode.rec
      (motive_1 := fun _ _ _ _ _ actual => ∃ calls, NodeCount actual calls)
      (motive_2 := fun _ _ _ _ _ _ actual => ∃ calls, ChildrenCount actual calls)
      (motive_3 := fun _ _ _ _ _ actual => ∃ calls, RowsCount actual calls)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase actual
  · constructor
    · intro entries offset values before results after actual
      exact EditChildren.rec
        (motive_1 := fun _ _ _ _ _ actual => ∃ calls, NodeCount actual calls)
        (motive_2 := fun _ _ _ _ _ _ actual => ∃ calls, ChildrenCount actual calls)
        (motive_3 := fun _ _ _ _ _ actual => ∃ calls, RowsCount actual calls)
        @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase actual
    · intro entries edges before results after actual
      exact EditRows.rec
        (motive_1 := fun _ _ _ _ _ actual => ∃ calls, NodeCount actual calls)
        (motive_2 := fun _ _ _ _ _ _ actual => ∃ calls, ChildrenCount actual calls)
        (motive_3 := fun _ _ _ _ _ actual => ∃ calls, RowsCount actual calls)
        @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase actual

/-- Every finite actual node graph has its own exact callback count. -/
theorem node_count {record originals edits value before result after}
    (actual : EditNode (width := width) record originals edits value before result after) :
    ∃ calls, NodeCount actual calls := counted.1 actual

/-- Every finite actual child graph retains the sum of its selected calls. -/
theorem children_count {record originals entries offset values before results after}
    (actual : EditChildren (width := width) record originals entries offset values before results after) :
    ∃ calls, ChildrenCount actual calls := counted.2.1 actual

/-- Every finite actual row graph retains all repeated row occurrences. -/
theorem rows_count {record originals entries edges before results after}
    (actual : EditRows (width := width) record originals entries edges before results after) :
    ∃ calls, RowsCount actual calls := counted.2.2 actual

/-- Every finite actual list graph has its exact ignored-leaf or child count. -/
theorem list_count {record originals edits values before results after}
    (actual : EditList (width := width) record originals edits values before results after) :
    ∃ calls, ListCount actual calls := by
  cases actual with
  | leaf => exact ⟨0, .leaf⟩
  | children actual =>
      obtain ⟨calls, counted⟩ := children_count actual
      exact ⟨calls, .children counted⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem edge_positions (value : EdgeValue Symbol Guard) :
    SourceCurrentAllocatedFiniteOrdinaryValuePositions.edge value = ChildPositions value.children := by
  cases value
  rfl

private def NodeBound {record originals edits value before result after}
    (_actual : EditNode (width := width) record originals edits value before result after) (calls : Nat) : Prop :=
  DNode value → calls ≤ Positions value

private def ChildrenBound {record originals entries offset values before results after}
    (_actual : EditChildren (width := width) record originals entries offset values before results after) (calls : Nat) : Prop :=
  DChildren values → calls ≤ ChildPositions values

private def RowsBound {record originals entries edges before results after}
    (_actual : EditRows (width := width) record originals entries edges before results after) (calls : Nat) : Prop :=
  DRows edges → calls ≤ RowPositions edges

private theorem bounded {record originals} :
    (∀ {edits value before result after calls} {actual : EditNode (width := width) record originals edits value before result after},
      NodeCount actual calls → NodeBound actual calls) ∧
    (∀ {entries offset values before results after calls} {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenCount actual calls → ChildrenBound actual calls) ∧
    (∀ {entries edges before results after calls} {actual : EditRows (width := width) record originals entries edges before results after},
      RowsCount actual calls → RowsBound actual calls) := by
  have leafCase : ∀ {target value} {before : SharedState width} {result} {after : SharedState width}
      (actual : Leaf record originals target value before result after),
      NodeBound (.leaf actual) 1 := by
    intro target value before result after actual _
    exact SourceCurrentAllocatedFiniteOrdinaryValuePositions.node_pos _
  have emptyCase : ∀ {entries state},
      NodeBound (.empty (width := width) (record := record) (originals := originals) (entries := entries) (state := state)) 0 := by
    intros
    intro _domain
    exact Nat.zero_le _
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap calls entry depth free}
      {actual : EditRows (width := width) record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)}
      (counted : RowsCount actual calls), RowsBound actual calls →
        NodeBound (.ordinary (entry := entry) (depth := depth) (free := free) actual built) calls := by
    intro entries edges before rebuilt middle value heap calls entry depth free actual built _ ih domain
    exact Nat.le_trans (ih domain.rows) (Nat.le_add_left _ _)
  have recursiveCase : ∀ {original exposed heap entries before value after calls}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode (width := width) record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      (counted : NodeCount body calls), NodeBound body calls → NodeBound (.recursive recursive head body) calls := by
    intro original exposed heap entries before value after calls recursive head body _ _ domain
    cases domain <;> cases recursive
  have nilChildren : ∀ {entries offset state},
      ChildrenBound (.nil (width := width) (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) 0 := by
    intros
    intro _domain
    exact Nat.zero_le _
  have unselectedCase : ∀ {entries values before results after calls value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren (width := width) record originals entries (offset + 1) values before results after}
      (counted : ChildrenCount rest calls), ChildrenBound rest calls →
        ChildrenBound (.unselected (value := value) offset absent rest) calls := by
    intro entries values before results after calls value offset absent rest _ ih domain
    cases domain with
    | cons _ tail => exact Nat.le_trans (ih tail) (Nat.le_add_left _ _)
  have selectedCase : ∀ {entries edits value before result middle values results after firstCalls restCalls} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode (width := width) record originals edits value before result middle}
      {rest : EditChildren (width := width) record originals entries (offset + 1) values middle results after}
      (head : NodeCount first firstCalls) (tail : ChildrenCount rest restCalls),
      NodeBound first firstCalls → ChildrenBound rest restCalls →
        ChildrenBound (.selected offset found first rest) (firstCalls + restCalls) := by
    intro entries edits value before result middle values results after firstCalls restCalls offset found first rest _ _ firstIH restIH domain
    cases domain with
    | cons head tail => exact Nat.add_le_add (firstIH head) (restIH tail)
  have nilRows : ∀ {entries state},
      RowsBound (.nil (width := width) (record := record) (originals := originals) (entries := entries) (state := state)) 0 := by
    intros
    intro _domain
    exact Nat.zero_le _
  have consCase : ∀ {entries before values middle result heap edges results after firstCalls restCalls} {edge : EdgeValue Symbol Guard}
      {children : EditChildren (width := width) record originals entries 0 edge.children before values middle}
      {built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows (width := width) record originals entries edges (advanceHeap middle heap) results after}
      (head : ChildrenCount children firstCalls) (tail : RowsCount rest restCalls),
      ChildrenBound children firstCalls → RowsBound rest restCalls →
        RowsBound (.cons children built rest) (firstCalls + restCalls) := by
    intro entries before values middle result heap edges results after firstCalls restCalls edge children built rest _ _ firstIH restIH domain
    cases domain with
    | cons first rest =>
        have headBound := firstIH first
        rw [← edge_positions] at headBound
        exact Nat.add_le_add headBound (restIH rest)
  constructor
  · intro edits value before result after calls actual own
    exact NodeCount.rec
      (motive_1 := fun {_ _ _ _ _} actual calls _ => NodeBound actual calls)
      (motive_2 := fun {_ _ _ _ _ _} actual calls _ => ChildrenBound actual calls)
      (motive_3 := fun {_ _ _ _ _} actual calls _ => RowsBound actual calls)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase own
  · constructor
    · intro entries offset values before results after calls actual own
      exact ChildrenCount.rec
        (motive_1 := fun {_ _ _ _ _} actual calls _ => NodeBound actual calls)
        (motive_2 := fun {_ _ _ _ _ _} actual calls _ => ChildrenBound actual calls)
        (motive_3 := fun {_ _ _ _ _} actual calls _ => RowsBound actual calls)
        @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase own
    · intro entries edges before results after calls actual own
      exact RowsCount.rec
        (motive_1 := fun {_ _ _ _ _} actual calls _ => NodeBound actual calls)
        (motive_2 := fun {_ _ _ _ _ _} actual calls _ => ChildrenBound actual calls)
        (motive_3 := fun {_ _ _ _ _} actual calls _ => RowsBound actual calls)
        @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase own

/-- Finite ordinary node callbacks fit the original input's literal positions. -/
theorem NodeCount.bound {record originals edits value before result after calls}
    {actual : EditNode (width := width) record originals edits value before result after}
    (counted : NodeCount actual calls) (domain : DNode value) : calls ≤ Positions value := bounded.1 counted domain

/-- Ordered child callbacks fit the original forest, including Empty roots. -/
theorem ChildrenCount.bound {record originals entries offset values before results after calls}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (counted : ChildrenCount actual calls) (domain : DChildren values) : calls ≤ ChildPositions values := bounded.2.1 counted domain

/-- Ordered row callbacks fit all original row child positions. -/
theorem RowsCount.bound {record originals entries edges before results after calls}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (counted : RowsCount actual calls) (domain : DRows edges) : calls ≤ RowPositions edges := bounded.2.2 counted domain

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
