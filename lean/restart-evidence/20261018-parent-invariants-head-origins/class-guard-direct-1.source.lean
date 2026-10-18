import MicroCFTA.SourceCurrentClassPassPhaseLineage
import MicroCFTA.SourceCurrentParentRowWriterLineage
import MicroCFTA.SourceCurrentNativeQueryRowOrigins

/-!
# Full guard origins through actual class edits

Ordinary reconstruction retains the complete source guard. Leaf queries
and recursive Head exposure supply new root rows. The source relation
records those actual events before composition through the class fold.
-/
namespace MicroCFTA.SourceCurrentClassFoldGuardOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A literal input row supplies the complete guard. -/
def Original (value : Value Symbol Guard) (field : Guard) : Prop :=
  ∃ row ∈ nodeEdges value, row.entry.key.constraint = field

/-- A leaf source retains its exact target query and the selected full row. -/
def LeafSource (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {record originals path input before result after}
    (actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf (width := width)
      record originals path input before result after) (field : Guard) : Prop :=
  ∃ (memos final : Memos),
    SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final ∧
    ∃ target middle forceInventory next base,
      SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver forceInventory record originals base path
        before target middle memos final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result after.checked final ∧
      after = SourceCurrentAllocatedSharedTargetState.advance middle after.checked ∧
      ∃ rowIndex row, (nodeEdges result)[rowIndex]? = some row ∧ row.entry.key.constraint = field ∧
        SourceCurrentNativeQueryRowOrigins.RowOrigin after.checked
          ⟨IntersectionEmptyDomain.emptyDomain,target,input⟩ result rowIndex row

/-- A root field event occurs in the exact node edit that returns it. -/
inductive NodeEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (field : Guard) :
    {record : Record} → {originals : List (Value Symbol Guard)} → {edits : Edits EqualityNormalize.Path} →
    {input : Value Symbol Guard} → {before : SharedState width} → {result : Value Symbol Guard} →
    {after : SharedState width} → EditNode record originals edits input before result after → Prop where
  /-- An actual leaf query supplies its returned row field. -/
  | leaf {record originals path input before result after}
      {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals path input before result after}
      (source : LeafSource formulas solver actual field) : NodeEvent formulas solver field (.leaf actual)
  /-- A selected exposed row supplies its field before the below edit. -/
  | exposed {record originals entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      {memos current : Memos} (read : SourceCurrentRequiredQueryMemos.HeadReads head memos current)
      (source : Original exposed field) : NodeEvent formulas solver field (.recursive recursive head body)
  /-- A later root field event remains inside the same actual Head branch. -/
  | recursive {record originals entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      (source : NodeEvent formulas solver field body) : NodeEvent formulas solver field (.recursive recursive head body)

/-- Actual leaf reads derive a full-field source without a caller-supplied row law. -/
theorem leaf_source {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record originals path input before result after memos final}
    {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf (width := width) record originals path input before result after}
    (reads : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
    (history : History before.checked) (closed : input.free = [])
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges result) :
    LeafSource formulas solver actual row.entry.key.constraint := by
  obtain ⟨index,present⟩ := List.mem_iff_getElem?.mp selected
  obtain ⟨target,middle,forceInventory,next,base,force,query,same,_,origin⟩ :=
    SourceCurrentNativeQueryRowOrigins.leaf reads history closed index row present
  exact ⟨memos,final,reads,target,middle,forceInventory,next,base,force,query,same,index,row,present,rfl,origin⟩

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after)
    (memos : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ row ∈ nodeEdges result, Original input row.entry.key.constraint ∨ NodeEvent formulas solver row.entry.key.constraint actual

end MicroCFTA.SourceCurrentClassFoldGuardOrigins
