import MicroCFTA.SourceCurrentClassFoldRowOrigins
import MicroCFTA.SourceCurrentRequiredRowOrigins

/-!
# Structural row occurrences through actual class edits

An occurrence either retains a complete original row or descends from an
actual native leaf or Head exposure. Ordinary event lifts retain the
canonical output index, raw row index, and exact child execution slice.
-/
namespace MicroCFTA.SourceCurrentClassStructuralOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentRequiredRowOrigins (RowAt Position)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

mutual
/-- An actual native leaf or Head exposure supplies this event value. -/
inductive Event (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List Node} → {edits : Edits EqualityNormalize.Path} →
    {input : Node} → {before : SharedState width} → {result : Node} → {after : SharedState width} →
    EditNode record originals edits input before result after → Node → Prop where
  /-- The native leaf supplies its actual returned value. -/
  | leaf {record originals path input before result after memos final}
      {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals path input before result after}
      (read : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
      (history : History before.checked) : Event formulas solver base (.leaf actual) result
  /-- Head supplies its exposed value before the recursive edit. -/
  | head {record originals entries original before exposed heap result after memos current final}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after}
      (read : SourceCurrentRequiredQueryMemos.HeadReads head memos current)
      (bodyRead : NodeReads formulas solver base body current final)
      (history : History before.checked) : Event formulas solver base (.recursive recursive head body) exposed
  /-- A recursive edit retains an event from its actual body call. -/
  | recursive {record originals entries original before exposed heap result after event}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after}
      (source : Event formulas solver base body event) :
      Event formulas solver base (.recursive recursive head body) event
  /-- A canonical survivor retains distinct output and raw source indices. -/
  | ordinary {record originals entries edges before rebuilt middle value heap entry depth free event}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value,heap)}
      {memos final : Memos} (read : RowsReads formulas solver base actual memos final)
      (outputIndex rawIndex childIndex : Nat) (parent : Edge)
      (output : (nodeEdges value)[outputIndex]? = some parent)
      (raw : rebuilt[rawIndex]? = some parent)
      (source : RowEvent formulas solver base actual rawIndex childIndex event) :
      Event formulas solver base (.ordinary (entry := entry) (depth := depth) (free := free) actual built) event

/-- The indexed child event retains its actual ordered dispatch. -/
inductive ChildEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List Node} → {entries : List (Int × Edits EqualityNormalize.Path)} →
    {offset : Nat} → {inputs : List Node} → {before : SharedState width} →
    {results : List Node} → {after : SharedState width} →
    EditChildren record originals entries offset inputs before results after → Nat → Node → Prop where
  /-- The selected current child supplies its actual node event. -/
  | here {record originals entries value before result middle values results after edits event} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after}
      (source : Event formulas solver base first event) :
      ChildEvent formulas solver base (.selected offset found first rest) 0 event
  /-- An earlier unselected child precedes the event. -/
  | unselected {record originals entries value values before results after index event} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset+1) values before results after}
      (source : ChildEvent formulas solver base rest index event) :
      ChildEvent formulas solver base (.unselected (value := value) offset absent rest) (index+1) event
  /-- An earlier selected child precedes the event. -/
  | selected {record originals entries value before result middle values results after edits index event} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after}
      (source : ChildEvent formulas solver base rest index event) :
      ChildEvent formulas solver base (.selected offset found first rest) (index+1) event

/-- The raw row event retains its exact selected child slice. -/
inductive RowEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List Node} → {entries : List (Int × Edits EqualityNormalize.Path)} →
    {inputs : List Edge} → {before : SharedState width} → {results : List Edge} → {after : SharedState width} →
    EditRows record originals entries inputs before results after → Nat → Nat → Node → Prop where
  /-- The current row retains the selected child and its complete execution slice. -/
  | here {record originals entries before values middle result heap edges results after edge event}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result,heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
      {memos current : Memos} (read : ChildrenReads formulas solver base children memos current)
      (childIndex : Nat) (child : Node) (selected : values[childIndex]? = some child)
      (slice : SourceCurrentSharedEditChildLineage.Slice formulas solver base record originals entries 0
        edge.children before values middle memos current childIndex child)
      (source : ChildEvent formulas solver base children childIndex event) :
      RowEvent formulas solver base (.cons children built rest) 0 childIndex event
  /-- A later row retains its distinct raw scan index. -/
  | later {record originals entries before values middle result heap edges results after edge rowIndex childIndex event}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result,heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
      (source : RowEvent formulas solver base rest rowIndex childIndex event) :
      RowEvent formulas solver base (.cons children built rest) (rowIndex+1) childIndex event
end

private def Source (input : Node) (row : Edge) : Prop :=
  ∃ path index original, RowAt input path index original ∧ RowOrigin original row

private def FromEvent {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after) (row : Edge) : Prop :=
  ∃ event path index original, Event formulas solver base actual event ∧
    RowAt event path index original ∧ RowOrigin original row

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ path index row, RowAt result path index row → Source input row ∨ FromEvent (formulas := formulas) (solver := solver) (base := base) actual row

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ childIndex child, results[childIndex]? = some child → ∀ path index row, RowAt child path index row →
    (∃ original, inputs[childIndex]? = some original ∧ Source original row) ∨
      ∃ event suffix sourceIndex original, ChildEvent formulas solver base actual childIndex event ∧
        RowAt event suffix sourceIndex original ∧ RowOrigin original row

private def RowsLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries inputs before results after}
    (actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ rawIndex output, results[rawIndex]? = some output →
    ∃ original, inputs[rawIndex]? = some original ∧ RowOrigin original output ∧
      ∀ childIndex child, output.children[childIndex]? = some child → ∀ path index row, RowAt child path index row →
      (∃ inputChild, original.children[childIndex]? = some inputChild ∧ Source inputChild row) ∨
        ∃ event suffix sourceIndex source, RowEvent formulas solver base actual rawIndex childIndex event ∧
          RowAt event suffix sourceIndex source ∧ RowOrigin source row

end MicroCFTA.SourceCurrentClassStructuralOrigins
