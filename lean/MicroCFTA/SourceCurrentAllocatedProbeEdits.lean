import MicroCFTA.SourceCurrentAllocatedProbeTargets
import MicroCFTA.SourceCurrentAllocatedSharedEditEffects

/-!
# Filtered probes through actual simultaneous class edits

The proof follows annotated actual leaves, head reads, and raw constructors.
The existing selected-path domain derives each reached physical input.
Unselected siblings can remain open. No future probe invariant is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeEdits
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualityProjectionPathDomain
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetForce (Retains)
open SourceCurrentAllocatedSharedEditGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

open InternedFreshOrdinaryProbeHeap (Heap)
open SourceCurrentAllocatedSharedEditEffects (node_physical edge_physical head_physical ListSafe)
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : HeapState}

private def NodeLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState width)
    (_result : Value Symbol Guard) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → Valid before.checked.native.machine.heap memos →
    Values base originals → Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

private def ChildrenLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (inputs : List (Value Symbol Guard))
    (before : SharedState width) (_results : List (Value Symbol Guard)) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

private def RowsLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (inputs : List (EdgeValue Symbol Guard))
    (before : SharedState width) (_results : List (EdgeValue Symbol Guard)) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

set_option maxHeartbeats 1600000 in
private theorem effects :
    (∀ {record originals edits value before result after} {memos final : Memos}
      {actual : EditNode (width := width) record originals edits value before result after},
      NodeReads formulas solver base actual memos final →
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final) ∧
    (∀ {record originals entries offset values before results after} {memos final : Memos}
      {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenReads formulas solver base actual memos final →
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final) ∧
    (∀ {record originals entries edges before results after} {memos final : Memos}
      {actual : EditRows (width := width) record originals entries edges before results after},
      RowsReads formulas solver base actual memos final →
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final) := by
  have leafCase : ∀ {next record originals path value before result after memos saved},
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path value before result after memos saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals (.editAt path) value before result after memos saved := by
    intro next record originals path value before result after memos saved receipt inventory populated nonempty allowed ready available safe valid known probes
    exact SourceCurrentAllocatedProbeTargets.leaf_heap receipt.reads ready known probes
  have emptyCase : ∀ {record originals entries state memos},
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.empty : Value Symbol Guard) state .empty state memos memos := by
    intro record originals entries state memos inventory populated nonempty allowed ready available safe valid known probes
    exact probes
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before rebuilt middle memos saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) memos saved := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
      inventory populated nonempty allowed ready available safe valid known probes
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have middleProbes := ih inventory populated allowed ready
      (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident) (ordinary_rows safe) valid known probes
    change Heap heap
    simpa only [built] using InternedFreshOrdinaryProbeHeap.node rebuilt middle.checked.native.machine.heap middleProbes
  have recursiveCase : ∀ {record originals memos current saved entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after},
      SourceCurrentRequiredQueryMemos.HeadReads head memos current →
      GlobalEffect before.checked.native.machine.heap heap memos current →
      NodeReads formulas solver base body current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) exposed (advanceHeap before heap) value after current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) original before value after memos saved := by
    intro record originals memos current saved entries original before exposed heap value after recursive head body
      headRead headGlobal bodyRead ih inventory populated nonempty allowed ready available safe valid known probes
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    exact ih inventory populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid known
      (SourceCurrentAllocatedProbeExposure.head_heap head ready.checked.semantic available probes)
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset
        ([] : List (Value Symbol Guard)) state [] state memos memos := by
    intro record originals entries offset state memos inventory populated allowed ready available safe valid known probes
    exact probes
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values before results after memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (value :: results) after memos saved := by
    intro record originals memos saved entries values before results after value offset absent rest read ih
      inventory populated allowed ready available safe valid known probes
    exact ih inventory populated allowed ready
      (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe) valid known probes
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result middle memos current →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values middle results after current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (result :: results) after memos saved := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstRead restRead firstIH restIH inventory populated allowed ready available safe valid known probes
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have firstProbes := firstIH inventory (children _ _ member).1 (children _ _ member).2 childAllowed
      ready (available _ List.mem_cons_self) (safe 0 _ (by simpa using found) value rfl) valid known probes
    obtain ⟨middleInventory, firstReceipt⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstRead
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self)
      (safe 0 _ (by simpa using found) value rfl) valid
    exact restIH middleInventory populated allowed firstReceipt.ready
      (fun original member => firstReceipt.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (children_tail safe) firstReceipt.globals.valid known firstProbes
  have nilRows : ∀ {record originals entries state memos},
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries
        ([] : List (EdgeValue Symbol Guard)) state [] state memos memos := by
    intro record originals entries state memos inventory populated allowed ready available safe valid known probes
    exact probes
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after edge}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries 0 edge.children before values middle memos current →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges (advanceHeap middle heap) results after current saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (edge :: edges) before (result :: results) after memos saved := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      firstRead restRead firstIH restIH inventory populated allowed ready resident safe valid known probes
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have firstProbes := firstIH inventory populated allowed ready available (safe _ List.mem_cons_self) valid known probes
    obtain ⟨middleInventory, first⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects firstRead
      populated allowed ready available (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows first.effects.grows
    have rebuiltPhysical := edge_physical first.ready edge.entry.key.symbol edge.entry.key.constraint values field first.available
    have edgeResult : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) ∧
        Effects (physical middle.checked) (physical (advanceHeap middle heap).checked) ∧
        InternedEdgeResidency.EdgeResident heap result ∧ result.children = values := by
      simpa only [rebuilt] using rebuiltPhysical
    have edgeProbes : Heap heap := by
      simpa only [rebuilt] using InternedFreshOrdinaryProbeHeap.edge edge.entry.key.symbol edge.entry.key.constraint values
        middle.checked.native.machine.heap firstProbes
    have edgeValid : Valid heap current := SourceQueryUnfoldMemo.valid_grows _ _ first.ready.checked.semantic
      edgeResult.2.1.keeps current first.globals.valid
    exact restIH middleInventory populated allowed edgeResult.1
      (fun original member => InternedEdgeResidency.edge_grows _ _ (first.effects.keeps.trans edgeResult.2.1.keeps).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) edgeValid known edgeProbes
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits value before result after memos final actual reads
    exact NodeReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries offset values before results after memos final actual reads
    exact ChildrenReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries edges before results after memos final actual reads
    exact RowsReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads

/-- Actual node edits retain probes through each annotated reached leaf and head. -/
theorem node_heap {edits value before result after memos final}
    {actual : EditNode (width := width) record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (probes : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap :=
  effects.1 reads inventory populated nonempty allowed ready available safe valid known probes

/-- Actual child edits retain probes without closing unselected siblings. -/
theorem children_heap {entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (probes : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap :=
  effects.2.1 reads inventory populated allowed ready available safe valid known probes

/-- Actual row edits retain probes through raw same-arity reconstruction. -/
theorem rows_heap {entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (probes : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap :=
  effects.2.2 reads inventory populated allowed ready available safe valid known probes

/-- Ignored root callbacks and actual below-edits preserve probes. -/
theorem list_heap {edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (probes : Heap before.checked.native.machine.heap) : Heap after.checked.native.machine.heap := by
  cases reads with
  | leaf => exact probes
  | children read => exact children_heap read populated allowed ready available safe valid known probes

end MicroCFTA.SourceCurrentAllocatedProbeEdits
