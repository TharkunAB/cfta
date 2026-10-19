import MicroCFTA.SourceCurrentClassRecursiveValueOrigins
import MicroCFTA.SourceCurrentSharedLeafNativeLineage

/-!
# Actual executions at structural event sources

An event retains its actual native request or Head and body edit. Its
available value has a supported heap and an actual later heap interval.
Literal recursive occurrences do not assert a projection of the whole
event or an observational origin through stored Mu bodies.
-/
namespace MicroCFTA.SourceCurrentClassEventExecutions
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentClassStructuralOrigins (Event ChildEvent RowEvent)
open SourceCurrentClassRecursiveValueOrigins (Occurs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A supported event retains its exact native or Head execution and later physical interval. -/
def Source (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (event : Node) (reader : Heap) : Prop :=
  ∃ eventHeap, SemanticReady eventHeap ∧ CostHeap eventHeap ∧ Available eventHeap event ∧ Keeps eventHeap reader ∧
    ((∃ record originals path input (before middle : SharedState width) target (finished : Checked width)
        forceInventory next base memos final,
      SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver forceInventory record originals base path
        before target middle memos final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked event finished final ∧
      eventHeap = finished.native.machine.heap ∧ input.free = [] ∧
      History before.checked ∧ History middle.checked ∧ History finished ∧
      ∃ fuel, Trace fuel (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input))
        middle.checked (.code (.pure event)) finished ∧
      ∃ handle, finished.native.nodes.cells handle = some ⟨⟨IntersectionEmptyDomain.emptyDomain,target,input⟩,.returned event⟩ ∧
        SourceCurrentNativeWriterReadyRetention.Written (width := width) handle
          ⟨IntersectionEmptyDomain.emptyDomain,target,input⟩ event finished.native) ∨
    (∃ record originals entries original (before : SharedState width) heap result (after : SharedState width)
        base inventory memos current final,
      ∃ head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap event heap,
      ∃ body : EditNode record originals (.editBelow entries) event (advanceHeap before heap) result after,
        SourceCurrentRequiredQueryMemos.HeadReads head memos current ∧
        NodeReads formulas solver base body current final ∧
        SharedReady formulas solver inventory record originals base before ∧
        Available before.checked.native.machine.heap original ∧ original.free = [] ∧
        History before.checked ∧ eventHeap = heap))

/-- A later actual physical interval retains the same captured execution. -/
theorem Source.later {formulas solver event before after}
    (source : Source (width := width) formulas solver event before) (later : Keeps before after) :
    Source (width := width) formulas solver event after := by
  obtain ⟨heap,semantic,costs,available,earlier,actual⟩ := source
  exact ⟨heap,semantic,costs,available,earlier.trans later,actual⟩

/-- Literal ordinary-child occurrences derive their own availability at the event heap. -/
theorem occurrence {event : Node} {path needle} (actual : Occurs event path needle)
    {heap : Heap} (semantic : SemanticReady heap) (available : Available heap event) : Available heap needle := by
  induction actual with
  | root => exact available
  | child rowIndex childIndex row child selected chosen rest ih =>
    have edges := resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ available.resident
    exact ih (semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row
      (edges row (List.mem_of_getElem? selected)) child (List.mem_of_getElem? chosen))

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ event, Event formulas solver base actual event → Source (width := width) formulas solver event after.checked.native.machine.heap

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ index event, ChildEvent formulas solver base actual index event → Source (width := width) formulas solver event after.checked.native.machine.heap

private def RowsLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries inputs before results after}
    (actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ rowIndex childIndex event, RowEvent formulas solver base actual rowIndex childIndex event →
      Source (width := width) formulas solver event after.checked.native.machine.heap

set_option maxHeartbeats 2400000 in
private theorem node_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final) : NodeLaw formulas solver base actual memos := by
  refine NodeReads.rec
    (motive_1 := fun {record originals edits input before result after} actual memos _ _ =>
      NodeLaw formulas solver base actual memos)
    (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
      ChildrenLaw formulas solver base actual memos)
    (motive_3 := fun {record originals entries inputs before results after} actual memos _ _ =>
      RowsLaw formulas solver base actual memos)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path input before result after memos saved receipt
      inventory populated nonempty allowed ready available safe valid history event source
    cases source with
    | leaf read eventHistory =>
      have closed : input.free = [] := by
        simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using safe [] path (by simp [leaves])
      obtain ⟨target,middle,forceInventory,next,base,forced,query,same,slot,middleHistory,afterHistory,
        middleGood,afterGood,firstGrowth,lastGrowth,origin⟩ :=
        SourceCurrentSharedLeafNativeLineage.leaf read eventHistory
      have returned := origin.returned forced.closed closed
      refine ⟨after.checked.native.machine.heap,receipt.ready.checked.semantic,receipt.ready.checked.costs,
        receipt.available,pure_keeps _ receipt.ready.checked.semantic.ready,Or.inl ?_⟩
      refine ⟨record,originals,path,input,before,middle,target,after.checked,forceInventory,next,base,
        _,_,forced,query,rfl,closed,eventHistory,middleHistory,afterHistory,?_⟩
      cases query.actual with
      | run trace => exact ⟨_,trace,returned⟩
  · intro record originals entries state memos inventory populated nonempty allowed ready available safe valid history event source
    cases source
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
      inventory populated nonempty allowed ready available safe valid history event source
    cases source with
    | ordinary eventRead outputIndex rawIndex childIndex parent output raw eventAt =>
      have facts := ready.checked.semantic.ready.semantic.1.normal.facts
      have resident := resident_edges _ facts.linked _ available.resident
      obtain ⟨next,receipt⟩ := rows_effects read populated allowed ready resident (ordinary_rows safe) valid
      have finish := node_physical receipt.ready rebuilt receipt.available
      have kept : Keeps middle.checked.native.machine.heap heap := by simpa only [built] using finish.2.1.keeps
      exact (ih inventory populated allowed ready resident (ordinary_rows safe) valid history
        rawIndex childIndex event eventAt).later kept
  · intro record originals memos current saved entries original before exposed heap value after recursive head body
      headRead headGlobal bodyRead ih inventory populated nonempty allowed ready available safe valid history event source
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    obtain ⟨next,receipt⟩ := node_effects bodyRead populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
    cases source with
    | head eventRead eventBody eventHistory =>
      exact ⟨heap,first.1.checked.semantic,first.1.checked.costs,first.2.2,receipt.effects.keeps,Or.inr
        ⟨record,originals,entries,original,before,heap,value,after,base,inventory,_,_,_,head,body,
          eventRead,eventBody,ready,available,closed,eventHistory,rfl⟩⟩
    | recursive eventAt =>
      exact ih inventory populated nonempty allowed first.1 first.2.2
        (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
        (history.advance _ headGlobal.keeps.growth) event eventAt
  · intro record originals entries offset state memos inventory populated allowed ready available safe valid history index event source
    cases source
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      inventory populated allowed ready available safe valid history index event source
    cases source with
    | unselected eventAt =>
      exact ih inventory populated allowed ready
        (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) valid history _ event eventAt
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest
      firstRead restRead firstIH restIH inventory populated allowed ready available safe valid history index event source
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have support := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by
      rw [Allowed,All] at allowed
      exact allowed _ _ member
    have childSafe := safe 0 _ (by simpa using found) original rfl
    obtain ⟨next,receipt⟩ := node_effects firstRead support.1 support.2 childAllowed ready
      (available _ List.mem_cons_self) childSafe valid
    have nextAvailable := fun value member => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ member))
    obtain ⟨last,later⟩ := children_effects restRead populated allowed receipt.ready nextAvailable
      (children_tail safe) receipt.globals.valid
    cases source with
    | here eventAt =>
      exact (firstIH inventory support.1 support.2 childAllowed ready (available _ List.mem_cons_self)
        childSafe valid history event eventAt).later later.effects.keeps
    | selected eventAt =>
      have nextHistory := (SourceCurrentParentNativeHistory.edit_node firstRead history
        ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
      exact restIH next populated allowed receipt.ready nextAvailable (children_tail safe) receipt.globals.valid nextHistory _ event eventAt
  · intro record originals entries state memos inventory populated allowed ready resident safe valid history rowIndex childIndex event source
    cases source
  · intro record originals memos current saved entries before values middle result heap edges results after edge children built rest
      firstRead restRead firstIH restIH inventory populated allowed ready resident safe valid history rowIndex childIndex event source
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have childAvailable := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    obtain ⟨middleInventory,childrenReceipt⟩ := children_effects firstRead populated allowed ready childAvailable
      (safe _ List.mem_cons_self) valid
    have oneRead : RowsReads formulas solver base (EditRows.cons children built EditRows.nil) memos current :=
      .cons (rebuilt := built) firstRead .nil
    obtain ⟨next,firstReceipt⟩ := rows_effects oneRead populated allowed ready
      (fun row member => resident row (List.mem_cons.mpr (.inl (by simpa using member))))
      (fun row member => safe row (List.mem_cons.mpr (.inl (by simpa using member)))) valid
    obtain ⟨last,later⟩ := rows_effects restRead populated allowed firstReceipt.ready
      (fun row member => edge_grows _ _ firstReceipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ member)))
      (fun row member => safe row (List.mem_cons_of_mem _ member)) firstReceipt.globals.valid
    cases source with
    | here eventRead index child selected slice eventAt =>
      have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows childrenReceipt.effects.grows
      have edgeEffects := edge_physical childrenReceipt.ready edge.entry.key.symbol edge.entry.key.constraint values field childrenReceipt.available
      have edgeKeeps : Keeps middle.checked.native.machine.heap heap := by simpa only [built] using edgeEffects.2.1.keeps
      exact (firstIH inventory populated allowed ready childAvailable (safe _ List.mem_cons_self) valid history index event eventAt).later
        (edgeKeeps.trans later.effects.keeps)
    | later eventAt =>
      have nextHistory := (SourceCurrentParentNativeHistory.edit_rows oneRead history facts.coherent.valid).1
      exact restIH next populated allowed firstReceipt.ready
        (fun row member => edge_grows _ _ firstReceipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ member)))
        (fun row member => safe row (List.mem_cons_of_mem _ member)) firstReceipt.globals.valid nextHistory _ childIndex event eventAt

/-- Actual node reads derive the selected event's supported native or Head execution. -/
theorem node {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap input) (safe : Safe edits input)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    {event} (source : Event formulas solver base actual event) :
    Source (width := width) formulas solver event after.checked.native.machine.heap :=
  node_law reads inventory populated nonempty allowed ready available safe valid history event source

end MicroCFTA.SourceCurrentClassEventExecutions
