import MicroCFTA.SourceCurrentClassEventExecutions
import MicroCFTA.SourceCurrentParentPublicationHistory

/-!
# Physical publication histories at actual class event sources

The same event heap retains its actual native or Head execution and both
publication intervals. Each forward extension uses its actual operation.
Heap growth and native memo history do not supply publication history.
-/
namespace MicroCFTA.SourceCurrentClassEventPublications
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
variable {initialHeap : Heap}
local notation "PublicationHistory" => SourceCurrentNativeMuPublication.History

/-- A supported event retains its exact native or Head execution and later physical interval. -/
def Source (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (initialHeap : Heap) (event : Node) (reader : Heap) : Prop :=
  ∃ eventHeap, SemanticReady eventHeap ∧ CostHeap eventHeap ∧ Available eventHeap event ∧ Keeps eventHeap reader ∧
    Nonempty (PublicationHistory initialHeap eventHeap) ∧ Nonempty (PublicationHistory eventHeap reader) ∧
    ((∃ record originals path input, ∃ before middle : SharedState width, ∃ target, ∃ finished : Checked width,
      ∃ forceInventory next base memos final,
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
    (∃ record originals entries original, ∃ before : SharedState width, ∃ heap result, ∃ after : SharedState width,
      ∃ base inventory memos current final,
      ∃ head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap event heap,
      ∃ body : EditNode record originals (.editBelow entries) event (advanceHeap before heap) result after,
        SourceCurrentRequiredQueryMemos.HeadReads head memos current ∧
        NodeReads formulas solver base body current final ∧
        SharedReady formulas solver inventory record originals base before ∧
        Available before.checked.native.machine.heap original ∧ original.free = [] ∧
        History before.checked ∧ eventHeap = heap))

/-- The same actual event heap projects to the earlier supported execution receipt. -/
theorem Source.forget {formulas solver initialHeap event reader}
    (source : Source (width := width) formulas solver initialHeap event reader) :
    SourceCurrentClassEventExecutions.Source (width := width) formulas solver event reader := by
  obtain ⟨heap,semantic,costs,available,kept,_prefix,_interval,actual⟩ := source
  exact ⟨heap,semantic,costs,available,kept,actual⟩

/-- A later event view requires both actual physical Keeps and its publication interval. -/
theorem Source.later {formulas solver initialHeap event before after}
    (source : Source (width := width) formulas solver initialHeap event before) (later : Keeps before after)
    (published : Nonempty (PublicationHistory before after)) :
    Source (width := width) formulas solver initialHeap event after := by
  obtain ⟨heap,semantic,costs,available,earlier,initialPublished,⟨interval⟩,actual⟩ := source
  obtain ⟨next⟩ := published
  exact ⟨heap,semantic,costs,available,earlier.trans later,initialPublished,⟨.trans interval next⟩,actual⟩

private theorem node_unique {record originals edits input before first after second later}
    (one : EditNode (width := width) record originals edits input before first after)
    (two : EditNode record originals edits input before second later) : first = second ∧ after = later := by
  obtain ⟨fuel,done⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.node_uniform one
  obtain ⟨other,completed⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.node_uniform two
  exact SourceCurrentAllocatedSharedEditWorkerStability.edit_done_unique (done fuel (Nat.le_refl _)) (completed other (Nat.le_refl _))

private theorem children_unique {record originals entries offset inputs before first after second later}
    (one : EditChildren (width := width) record originals entries offset inputs before first after)
    (two : EditChildren record originals entries offset inputs before second later) : first = second ∧ after = later := by
  obtain ⟨fuel,done⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete one)
  obtain ⟨other,completed⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete two)
  exact SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_unique (done fuel (Nat.le_refl _)) (completed other (Nat.le_refl _))

private theorem rows_unique {record originals entries inputs before first after second later}
    (one : EditRows (width := width) record originals entries inputs before first after)
    (two : EditRows record originals entries inputs before second later) : first = second ∧ after = later := by
  obtain ⟨fuel,done⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.rows_complete one)
  obtain ⟨other,completed⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.rows_complete two)
  exact SourceCurrentAllocatedSharedEditWorkerStability.rows_edit_done_unique (done fuel (Nat.le_refl _)) (completed other (Nat.le_refl _))

private def NodeLaw (initialHeap : Heap) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (_actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  Values base originals → ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    PublicationHistory initialHeap before.checked.native.machine.heap → ∀ otherAfter (other : EditNode record originals edits input before result otherAfter),
      ∀ event, Event formulas solver base other event → Source (width := width) formulas solver initialHeap event after.checked.native.machine.heap

private def ChildrenLaw (initialHeap : Heap) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (_actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  Values base originals → ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    PublicationHistory initialHeap before.checked.native.machine.heap → ∀ otherAfter (other : EditChildren record originals entries offset inputs before results otherAfter),
      ∀ index event, ChildEvent formulas solver base other index event → Source (width := width) formulas solver initialHeap event after.checked.native.machine.heap

private def RowsLaw (initialHeap : Heap) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries inputs before results after}
    (_actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  Values base originals → ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    PublicationHistory initialHeap before.checked.native.machine.heap → ∀ otherAfter (other : EditRows record originals entries inputs before results otherAfter),
      ∀ rowIndex childIndex event, RowEvent formulas solver base other rowIndex childIndex event →
      Source (width := width) formulas solver initialHeap event after.checked.native.machine.heap

set_option maxHeartbeats 2400000 in
private theorem node_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final) : NodeLaw initialHeap formulas solver base actual memos := by
  refine NodeReads.rec
    (motive_1 := fun {record originals edits input before result after} actual memos _ _ =>
      NodeLaw initialHeap formulas solver base actual memos)
    (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
      ChildrenLaw initialHeap formulas solver base actual memos)
    (motive_3 := fun {record originals entries inputs before results after} actual memos _ _ =>
      RowsLaw initialHeap formulas solver base actual memos)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path input before result after memos saved receipt
      originalValues inventory populated nonempty allowed ready available safe valid history published otherAfter other event source
    have sameAfter := (node_unique (.leaf receipt.actual) other).2
    cases sameAfter
    cases source with
    | leaf read eventHistory =>
      have closed : input.free = [] := by
        simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using safe [] path (by simp [leaves])
      obtain ⟨target,middle,forceInventory,next,base,forced,query,same,slot,middleHistory,afterHistory,
        middleGood,afterGood,firstGrowth,lastGrowth,origin⟩ :=
        SourceCurrentSharedLeafNativeLineage.leaf read eventHistory
      have returned := origin.returned forced.closed closed
      obtain ⟨interval⟩ := SourceCurrentParentPublicationHistory.leaf receipt ready.checked
        (fun value member => ready.captured.available value (originalValues value member)) ready.stored
      refine ⟨after.checked.native.machine.heap,receipt.ready.checked.semantic,receipt.ready.checked.costs,
        receipt.available,pure_keeps _ receipt.ready.checked.semantic.ready,
        ⟨.trans published interval⟩,⟨.refl _⟩,Or.inl ?_⟩
      refine ⟨record,originals,path,input,before,middle,target,after.checked,forceInventory,next,base,
        _,_,forced,query,rfl,closed,eventHistory,middleHistory,afterHistory,?_⟩
      cases query.actual with
      | run trace => exact ⟨_,trace,returned⟩
  · intro record originals entries state memos originalValues inventory populated nonempty allowed ready available safe valid history published otherAfter other event source
    cases source <;> contradiction
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
      originalValues inventory populated nonempty allowed ready available safe valid history published otherAfter other event source
    cases source with
    | @ordinary _ _ _ otherRows otherMiddle _ otherHeap _ _ _ _ otherActual otherBuilt _ _ eventRead outputIndex rawIndex childIndex parent output raw eventAt =>
      obtain ⟨rfl,rfl⟩ := rows_unique actual otherActual
      have facts := ready.checked.semantic.ready.semantic.1.normal.facts
      have resident := resident_edges _ facts.linked _ available.resident
      obtain ⟨next,receipt⟩ := rows_effects read populated allowed ready resident (ordinary_rows safe) valid
      have finish := node_physical receipt.ready rebuilt receipt.available
      have kept : Keeps middle.checked.native.machine.heap heap := by
        have kept : Keeps middle.checked.native.machine.heap (run (makeNode rebuilt) middle.checked.native.machine.heap).2 := finish.2.1.keeps
        simpa only [built] using kept
      exact (ih originalValues inventory populated allowed ready resident (ordinary_rows safe) valid history published
        _ otherActual rawIndex childIndex event eventAt).later kept ⟨by
          have old := InternedShallowHeap.makeNode_noNewMu rebuilt middle.checked.native.machine.heap
          rw [built] at old
          exact .retain _ _ old⟩
    | head => contradiction
    | recursive => contradiction
  · intro record originals memos current saved entries original before exposed heap value after recursive head body
      headRead headGlobal bodyRead ih originalValues inventory populated nonempty allowed ready available safe valid history published otherAfter other event source
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    obtain ⟨next,receipt⟩ := node_effects bodyRead populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
    obtain ⟨headInterval⟩ := SourceCurrentRequiredPublicationHistory.head head ready.checked.semantic ready.checked.costs available
    have nextPublished := SourceCurrentNativeMuPublication.History.trans published headInterval
    cases source with
    | @head _ _ _ otherExposed otherHeap _ _ _ _ _ _ otherHead otherBody eventRead eventBody eventHistory =>
      obtain ⟨rfl,rfl⟩ := head.unique otherHead
      have sameAfter := (node_unique body otherBody).2
      cases sameAfter
      have bodyInterval := SourceCurrentParentPublicationHistory.node bodyRead originalValues
        inventory populated nonempty allowed first.1 first.2.2
        (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
      exact ⟨heap,first.1.checked.semantic,first.1.checked.costs,first.2.2,receipt.effects.keeps,
        ⟨nextPublished⟩,bodyInterval,Or.inr
        ⟨record,originals,entries,original,before,heap,value,after,base,inventory,_,_,_,otherHead,otherBody,
          eventRead,eventBody,ready,available,closed,eventHistory,rfl⟩⟩
    | @recursive _ _ _ otherExposed otherHeap _ _ _ _ otherHead otherBody eventAt =>
      obtain ⟨rfl,rfl⟩ := head.unique otherHead
      exact ih originalValues inventory populated nonempty allowed first.1 first.2.2
        (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
        (history.advance _ headGlobal.keeps.growth) nextPublished _ otherBody event eventAt
    | ordinary => contradiction
  · intro record originals entries offset state memos originalValues inventory populated allowed ready available safe valid history published otherAfter other index event source
    cases source
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      originalValues inventory populated allowed ready available safe valid history published otherAfter other index event source
    cases source with
    | unselected eventAt =>
      exact ih originalValues inventory populated allowed ready
        (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) valid history published _ _ _ event eventAt
    | here => simp_all
    | selected => simp_all
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest
      firstRead restRead firstIH restIH originalValues inventory populated allowed ready available safe valid history published otherAfter other index event source
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
    obtain ⟨firstInterval⟩ := SourceCurrentParentPublicationHistory.node firstRead originalValues
      inventory support.1 support.2 childAllowed ready (available _ List.mem_cons_self) childSafe valid
    have nextPublished := SourceCurrentNativeMuPublication.History.trans published firstInterval
    have tailInterval := SourceCurrentParentPublicationHistory.children restRead originalValues
      next populated allowed receipt.ready nextAvailable (children_tail safe) receipt.globals.valid
    cases source with
    | @here _ _ _ _ otherMiddle _ _ _ otherEdits _ _ otherFound otherFirst otherRest eventAt =>
      have sameEdits : otherEdits = edits := Option.some.inj (otherFound.symm.trans found)
      subst otherEdits
      have sameMiddle := (node_unique first otherFirst).2
      cases sameMiddle
      exact (firstIH originalValues inventory support.1 support.2 childAllowed ready (available _ List.mem_cons_self)
        childSafe valid history published _ otherFirst event eventAt).later later.effects.keeps tailInterval
    | @selected _ _ _ _ otherMiddle _ _ _ otherEdits _ _ _ otherFound otherFirst otherRest eventAt =>
      have sameEdits : otherEdits = edits := Option.some.inj (otherFound.symm.trans found)
      subst otherEdits
      have sameMiddle := (node_unique first otherFirst).2
      cases sameMiddle
      have nextHistory := (SourceCurrentParentNativeHistory.edit_node firstRead history
        ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
      exact restIH originalValues next populated allowed receipt.ready nextAvailable (children_tail safe) receipt.globals.valid nextHistory nextPublished _ otherRest _ event eventAt
    | unselected => simp_all
  · intro record originals entries state memos originalValues inventory populated allowed ready resident safe valid history published otherAfter other rowIndex childIndex event source
    cases source
  · intro record originals memos current saved entries before values middle result heap edges results after edge children built rest
      firstRead restRead firstIH restIH originalValues inventory populated allowed ready resident safe valid history published otherAfter other rowIndex childIndex event source
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
    obtain ⟨firstInterval⟩ := SourceCurrentParentPublicationHistory.rows oneRead originalValues inventory
      populated allowed ready
      (fun row member => resident row (List.mem_cons.mpr (.inl (by simpa using member))))
      (fun row member => safe row (List.mem_cons.mpr (.inl (by simpa using member)))) valid
    have nextPublished := SourceCurrentNativeMuPublication.History.trans published firstInterval
    obtain ⟨tailInterval⟩ := SourceCurrentParentPublicationHistory.rows restRead originalValues next
      populated allowed firstReceipt.ready
      (fun row member => edge_grows _ _ firstReceipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ member)))
      (fun row member => safe row (List.mem_cons_of_mem _ member)) firstReceipt.globals.valid
    cases source with
    | @here _ _ otherValues otherMiddle _ otherHeap _ _ _ _ _ otherChildren otherBuilt otherRest _ _ eventRead index child selected slice eventAt =>
      obtain ⟨rfl,rfl⟩ := children_unique children otherChildren
      have sameHeap := congrArg Prod.snd (built.symm.trans otherBuilt)
      dsimp only at sameHeap
      cases sameHeap
      have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows childrenReceipt.effects.grows
      have edgeEffects := edge_physical childrenReceipt.ready edge.entry.key.symbol edge.entry.key.constraint values field childrenReceipt.available
      have edgeKeeps : Keeps middle.checked.native.machine.heap heap := by
        have kept : Keeps middle.checked.native.machine.heap
            (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 := edgeEffects.2.1.keeps
        simpa only [built] using kept
      exact (firstIH originalValues inventory populated allowed ready childAvailable (safe _ List.mem_cons_self) valid history published _ otherChildren childIndex event eventAt).later
        (edgeKeeps.trans later.effects.keeps) ⟨by
          have old : InternedShallowHeap.NoNewMu middle.checked.native.machine.heap
              (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 := by
            intro key entry body depth ordinary stored
            exact stored
          rw [built] at old
          exact .trans (.retain _ _ old) tailInterval⟩
    | @later _ _ otherValues otherMiddle _ otherHeap _ _ _ _ _ _ _ otherChildren otherBuilt otherRest eventAt =>
      obtain ⟨rfl,rfl⟩ := children_unique children otherChildren
      have sameHeap := congrArg Prod.snd (built.symm.trans otherBuilt)
      dsimp only at sameHeap
      cases sameHeap
      have nextHistory := (SourceCurrentParentNativeHistory.edit_rows oneRead history facts.coherent.valid).1
      exact restIH originalValues next populated allowed firstReceipt.ready
        (fun row member => edge_grows _ _ firstReceipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ member)))
        (fun row member => safe row (List.mem_cons_of_mem _ member)) firstReceipt.globals.valid nextHistory nextPublished _ otherRest _ childIndex event eventAt

/-- Actual node reads derive the selected event's supported native or Head execution. -/
theorem node {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (originalValues : Values base originals)
    (inventory : Inventory) (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap input) (safe : Safe edits input)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (published : PublicationHistory initialHeap before.checked.native.machine.heap)
    {event} (source : Event formulas solver base actual event) :
    Source (width := width) formulas solver initialHeap event after.checked.native.machine.heap :=
  node_law reads originalValues inventory populated nonempty allowed ready available safe valid history published after actual event source

/-- Actual ordered child reads derive the same selected event execution and its final interval. -/
theorem children {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (originalValues : Values base originals)
    (inventory : Inventory) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (published : PublicationHistory initialHeap before.checked.native.machine.heap)
    {index event} (source : ChildEvent formulas solver base actual index event) :
    Source (width := width) formulas solver initialHeap event after.checked.native.machine.heap := by
  have law : ∀ {record originals entries offset values before results after memos final}
      {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenReads formulas solver base actual memos final → ChildrenLaw initialHeap formulas solver base actual memos := by
    intro record originals entries offset values before results after memos final actual reads
    refine ChildrenReads.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
        ChildrenLaw initialHeap formulas solver base actual memos)
      (motive_3 := fun _ _ _ _ => True)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
      ?_ ?_ ?_ (by intros; trivial) (by intros; trivial) reads
    · intro record originals entries offset state memos originalValues inventory populated allowed ready available safe valid history published otherAfter other index event source
      cases source
    · intro record originals memos saved entries values before results after original offset absent rest read ih
        originalValues inventory populated allowed ready available safe valid history published otherAfter other index event source
      cases source with
      | unselected eventAt =>
        exact ih originalValues inventory populated allowed ready
          (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) valid history published _ _ _ event eventAt
      | here => simp_all
      | selected => simp_all
    · intro record originals memos current saved entries edits original before result middle values results after offset found first rest
        firstRead restRead firstIH restIH originalValues inventory populated allowed ready available safe valid history published otherAfter other index event source
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
      obtain ⟨firstInterval⟩ := SourceCurrentParentPublicationHistory.node firstRead originalValues
        inventory support.1 support.2 childAllowed ready (available _ List.mem_cons_self) childSafe valid
      have nextPublished := SourceCurrentNativeMuPublication.History.trans published firstInterval
      have tailInterval := SourceCurrentParentPublicationHistory.children restRead originalValues
        next populated allowed receipt.ready nextAvailable (children_tail safe) receipt.globals.valid
      cases source with
      | @here _ _ _ _ otherMiddle _ _ _ otherEdits _ _ otherFound otherFirst otherRest eventAt =>
        have sameEdits : otherEdits = edits := Option.some.inj (otherFound.symm.trans found)
        subst otherEdits
        have sameMiddle := (node_unique first otherFirst).2
        cases sameMiddle
        exact ((node_law firstRead) originalValues inventory support.1 support.2 childAllowed ready (available _ List.mem_cons_self)
          childSafe valid history published _ otherFirst event eventAt).later later.effects.keeps tailInterval
      | @selected _ _ _ _ otherMiddle _ _ _ otherEdits _ _ _ otherFound otherFirst otherRest eventAt =>
        have sameEdits : otherEdits = edits := Option.some.inj (otherFound.symm.trans found)
        subst otherEdits
        have sameMiddle := (node_unique first otherFirst).2
        cases sameMiddle
        have nextHistory := (SourceCurrentParentNativeHistory.edit_node firstRead history
          ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
        exact restIH originalValues next populated allowed receipt.ready nextAvailable (children_tail safe) receipt.globals.valid nextHistory nextPublished _ otherRest _ event eventAt
      | unselected => simp_all
  exact law reads originalValues inventory populated allowed ready available safe valid history published after actual index event source

end MicroCFTA.SourceCurrentClassEventPublications
