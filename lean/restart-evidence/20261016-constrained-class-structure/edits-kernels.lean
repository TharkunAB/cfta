import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdits

namespace FiniteOrdinaryEditChecks
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
variable {base : HeapState}

/-- The current input supplies the leaf bound, independently of the captured target height. -/
theorem current_operand_bound {next : Inventory} {receiptBase : HeapState} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : SharedState width} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals receiptBase
      path input before result after memos final)
    (ready : Ready formulas solver inventory record originals base before) (known : Values base originals)
    (captured : DChildren originals) (stored : Stored before) (domain : DNode input) :
    Stored after ∧ DNode result ∧ MergedOrdinaryHeight.height result ≤ MergedOrdinaryHeight.height input :=
  SourceCurrentAllocatedFiniteOrdinaryReceiptStructure.leaf_receipt receipt ready known captured stored domain

/-- Historical force receipts need no equality between their base and the current capture base. -/
theorem historical_force_base {next : Inventory} {receiptBase : HeapState} {path : EqualityNormalize.Path}
    {value : Value Symbol Guard} {before after : SharedState width} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record originals receiptBase
      path before value after memos final)
    (ready : Ready formulas solver inventory record originals base before) (known : Values base originals)
    (captured : DChildren originals) (stored : Stored before) : Stored after ∧ DNode value :=
  SourceCurrentAllocatedFiniteOrdinaryReceiptStructure.force_receipt receipt ready known captured stored

/-- A supplied list receipt gives ordered bounds, output domain, and source arity together. -/
theorem positional_list {edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (captured : DChildren originals) (stored : Stored before) (domain : DChildren values) :
    Stored after ∧ DChildren results ∧ results.length = values.length ∧
      MergedOrdinaryHeight.childrenHeight results ≤ MergedOrdinaryHeight.childrenHeight values := by
  have result := SourceCurrentAllocatedFiniteOrdinaryEdits.list reads populated allowed ready available safe valid
    known captured stored domain
  exact ⟨result.1, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_domain result.2, result.2.length_eq.symm,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_height result.2⟩

/-- A second traversal uses the first traversal's actual inventory, residency, globals, and tables. -/
theorem two_lists {firstEdits nextEdits values middleValues results before middle after memos current final}
    {first : EditList (width := width) record originals firstEdits values before middleValues middle}
    {last : EditList (width := width) record originals nextEdits middleValues middle results after}
    (firstReads : ListReads formulas solver base first memos current)
    (lastReads : ListReads formulas solver base last current final)
    (firstPopulated : Populated firstEdits) (firstAllowed : Allowed record firstEdits)
    (lastPopulated : Populated nextEdits) (lastAllowed : Allowed record nextEdits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (firstSafe : SourceCurrentAllocatedSharedEditEffects.ListSafe firstEdits values)
    (lastSafe : SourceCurrentAllocatedSharedEditEffects.ListSafe nextEdits middleValues)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (captured : DChildren originals) (stored : Stored before) (domain : DChildren values) :
    Stored after ∧ All₂ NodeNarrow values results := by
  have firstResult := SourceCurrentAllocatedFiniteOrdinaryEdits.list firstReads firstPopulated firstAllowed ready
    available firstSafe valid known captured stored domain
  obtain ⟨next, firstReceipt⟩ := SourceCurrentAllocatedSharedEditEffects.list_effects firstReads firstPopulated
    firstAllowed ready available firstSafe valid
  have lastResult := SourceCurrentAllocatedFiniteOrdinaryEdits.list lastReads lastPopulated lastAllowed firstReceipt.ready
    firstReceipt.available lastSafe firstReceipt.globals.valid known captured firstResult.1
    (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_domain firstResult.2)
  exact ⟨lastResult.1, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_trans firstResult.2 lastResult.2⟩

/-- A root callback is ignored with no target range or native query premise. -/
theorem ignored_root {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)}
    {before : SharedState width} {memos : Memos}
    (member : path ∈ record.paths) (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (captured : DChildren originals) (stored : Stored before) (domain : DChildren values) :
    Stored before ∧ All₂ NodeNarrow values values := by
  have reads : ListReads formulas solver base (EditList.leaf (record := record) (originals := originals) (target := path) (values := values) (state := before)) memos memos := .leaf
  exact SourceCurrentAllocatedFiniteOrdinaryEdits.list reads (by simp [Populated])
    (by simpa only [Allowed, All] using member) ready available trivial valid known captured stored domain

/-- Raw ordinary reconstruction bounds the same actual result after all supplied row reads. -/
theorem ordinary_rows {entries edges before rebuilt middle result heap entry depth free memos final}
    {actual : EditRows (width := width) record originals entries edges before rebuilt middle}
    (reads : RowsReads formulas solver base actual memos final)
    (built : run (makeNode rebuilt) middle.checked.native.machine.heap = (result, heap))
    (populated : Populated (.editBelow entries)) (nonempty : HasLeaf (.editBelow entries))
    (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap (.node entry edges depth free))
    (safe : Safe (.editBelow entries) (.node entry edges depth free)) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (captured : DChildren originals) (stored : Stored before) (domain : DRows edges) :
    Stored (advanceHeap middle heap) ∧ NodeNarrow (.node entry edges depth free) result := by
  have nodeReads : NodeReads formulas solver base (EditNode.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos final :=
    .ordinary (built := built) reads
  exact SourceCurrentAllocatedFiniteOrdinaryEdits.node nodeReads populated nonempty allowed ready available safe valid
    known captured stored (.ordinary domain)

/-- Full row guards remain unrestricted while every original row position retains its bound. -/
theorem full_guard_rows {entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (captured : DChildren originals) (stored : Stored before) (domain : DRows edges) :
    Stored after ∧ DRows results ∧ results.length = edges.length ∧
      MergedOrdinaryHeight.edgesHeight results ≤ MergedOrdinaryHeight.edgesHeight edges := by
  have result := SourceCurrentAllocatedFiniteOrdinaryEdits.rows reads populated allowed ready available safe valid
    known captured stored domain
  exact ⟨result.1, SourceCurrentAllocatedFiniteOrdinaryNarrow.rows_domain result.2, result.2.length_eq.symm,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.rows_height result.2⟩

/-- The exact returned target slot remains admitted after every supplied edit list. -/
theorem returned_slot {edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (captured : DChildren originals) (stored : Stored before) (domain : DChildren values)
    (path : EqualityNormalize.Path) (value : Value Symbol Guard) (present : after.targets path = some value) : DNode value := by
  have result := SourceCurrentAllocatedFiniteOrdinaryEdits.list reads populated allowed ready available safe valid
    known captured stored domain
  exact result.1.slots path value present

#print axioms current_operand_bound
#check @current_operand_bound
#print axioms historical_force_base
#check @historical_force_base
#print axioms positional_list
#check @positional_list
#print axioms two_lists
#check @two_lists
#print axioms ignored_root
#check @ignored_root
#print axioms ordinary_rows
#check @ordinary_rows
#print axioms full_guard_rows
#check @full_guard_rows
#print axioms returned_slot
#check @returned_slot
end FiniteOrdinaryEditChecks
