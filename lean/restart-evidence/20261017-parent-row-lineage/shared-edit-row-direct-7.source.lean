import MicroCFTA.SourceCurrentAllocatedSharedEditEffects
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Indexed rows in actual shared class edits

Raw row reconstruction retains the original row index and full fields.
The result retains the actual ordered child calls and their captured heaps.
Node normalization can remove, reorder, or merge rows. Each surviving row
still has an indexed raw source. These results concern completed edits.
-/
namespace MicroCFTA.SourceCurrentSharedEditRowLineage
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every output child retains its original index and actual selected call. -/
theorem children_indexed {record originals entries offset values before results after}
    (actual : EditChildren (width := width) record originals entries offset values before results after)
    {index : Nat} {result : Value Symbol Guard} (selected : results[index]? = some result) :
    ∃ original, values[index]? = some original ∧
      ((SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = none ∧ result = original) ∨
        ∃ edits, ∃ start finish : SharedState width,
          SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = some edits ∧
          EditNode record originals edits original start result finish) := by
  have law : ∀ {record originals entries offset values before results after}
      (trace : EditChildren (width := width) record originals entries offset values before results after),
      ∀ index result, results[index]? = some result →
        ∃ original, values[index]? = some original ∧
          ((SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = none ∧ result = original) ∨
            ∃ edits, ∃ start finish : SharedState width,
              SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = some edits ∧
              EditNode record originals edits original start result finish) := by
    intro record originals entries offset values before results after trace
    exact EditChildren.rec
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun entries offset values _ results _ _ =>
        ∀ index result, results[index]? = some result →
          ∃ original, values[index]? = some original ∧
            ((SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = none ∧ result = original) ∨
              ∃ edits, ∃ start finish : SharedState width,
                SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = some edits ∧
                EditNode record originals edits original start result finish))
      (motive_3 := fun _ _ _ _ _ _ => True)
      (by intros; trivial) (by intros; trivial)
      (by intros; trivial) (by intros; trivial)
      (by intro entries offset state index result selected; simp at selected)
      (by
        intro entries values before results after value offset absent rest ih index result selected
        cases index with
        | zero =>
            have same : value = result := by simpa using selected
            exact ⟨value, rfl, Or.inl ⟨by simpa using absent, same.symm⟩⟩
        | succ index =>
            have found := ih index result (by simpa using selected)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found)
      (by
        intro entries edits value before result middle values results after offset found first rest _ ih index output selected
        cases index with
        | zero =>
            have same : result = output := by simpa using selected
            exact ⟨value, rfl, Or.inr ⟨edits, before, middle, by simpa using found, same ▸ first⟩⟩
        | succ index =>
            have selectedTail := ih index output (by simpa using selected)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using selectedTail)
      (by intros; trivial) (by intros; trivial) trace
  exact law actual index result selected

private def RowsLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width) (results : List (EdgeValue Symbol Guard))
    (after : SharedState width) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before →
    Edges before.checked.native.machine.heap edges → RowsSafe entries edges →
    Valid before.checked.native.machine.heap memos →
    ∀ (index : Nat) (result : EdgeValue Symbol Guard), results[index]? = some result →
      ∃ original : EdgeValue Symbol Guard, ∃ start middle : SharedState width, ∃ values heap startInventory middleInventory rowMemos rowFinal,
      ∃ call : EditChildren record originals entries 0 original.children start values middle,
        edges[index]? = some original ∧
        ChildrenReads formulas solver base call rowMemos rowFinal ∧
        Valid start.checked.native.machine.heap rowMemos ∧
        run (makeEdge original.entry.key.symbol original.entry.key.constraint values)
          middle.checked.native.machine.heap = (result, heap) ∧
        result.entry.key.symbol = original.entry.key.symbol ∧
        result.entry.key.constraint = original.entry.key.constraint ∧ result.children = values ∧
        Ready formulas solver startInventory record originals base start ∧
        Ready formulas solver middleInventory record originals base middle ∧
        Grows start.checked.native.machine.heap after.checked.native.machine.heap ∧
        Grows middle.checked.native.machine.heap after.checked.native.machine.heap ∧
        Grows heap after.checked.native.machine.heap

private theorem rows_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final) :
    RowsLaw formulas solver base record originals entries edges before results after memos := by
  have nilCase : ∀ {record originals entries state memos},
      RowsLaw (width := width) formulas solver base record originals entries [] state [] state memos := by
    intro record originals entries state memos inventory populated allowed ready resident safe valid index result selected
    simp at selected
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after edge}
      {children : EditChildren (width := width) record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      RowsLaw formulas solver base record originals entries edges (advanceHeap middle heap) results after current →
      RowsLaw formulas solver base record originals entries (edge :: edges) before (result :: results) after memos := by
    intro record originals memos current saved entries before values middle result heap edges results after edge
      children rebuilt rest firstRead restRead ih inventory populated allowed ready resident safe valid index output selected
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    obtain ⟨middleInventory, first⟩ := children_effects firstRead populated allowed ready
      (facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)) (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows first.effects.grows
    have raw := edge_physical first.ready edge.entry.key.symbol edge.entry.key.constraint values field first.available
    have edgeResult : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) ∧
        SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical middle.checked)
          (SourceCurrentAllocatedNativeEffects.physical (advanceHeap middle heap).checked) ∧
        InternedEdgeResidency.EdgeResident heap result ∧ result.children = values := by
      simpa only [rebuilt] using raw
    have nextValid : Valid heap current := SourceQueryUnfoldMemo.valid_grows _ _
      first.ready.checked.semantic edgeResult.2.1.keeps current first.globals.valid
    have preceding := first.effects.trans edgeResult.2.1
    have tailResident : Edges (advanceHeap middle heap).checked.native.machine.heap edges := by
      intro original member
      exact InternedEdgeResidency.edge_grows _ _ preceding.keeps.growth original
        (resident original (List.mem_cons_of_mem _ member))
    have tailSafe : RowsSafe entries edges := fun original member => safe original (List.mem_cons_of_mem _ member)
    cases index with
    | zero =>
        have same : result = output := by simpa using selected
        subst output
        obtain ⟨next, tail⟩ := rows_effects restRead populated allowed edgeResult.1 tailResident tailSafe nextValid
        have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.checked.native.machine.heap
          first.ready.checked.semantic.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint
          values first.available
        have exactFields : result.entry.key.symbol = edge.entry.key.symbol ∧
            result.entry.key.constraint = edge.entry.key.constraint ∧ result.children = values := by
          simpa only [rebuilt] using fields
        exact ⟨edge, before, middle, values, heap, inventory, middleInventory, memos, current, children,
          rfl, firstRead, valid, rebuilt,
          exactFields.1, exactFields.2.1, exactFields.2.2, ready, first.ready,
          (preceding.trans tail.effects).keeps.growth,
          (edgeResult.2.1.trans tail.effects).keeps.growth, tail.effects.keeps.growth⟩
    | succ index =>
        obtain ⟨original, start, rowMiddle, rowValues, rowHeap, startInventory, rowInventory,
          rowMemos, rowFinal, actualChildren, sourceIndex, actualReads, startValid, actualBuilt, symbol, guard, exactChildren, startReady, middleReady,
          startGrowth, middleGrowth, heapGrowth⟩ :=
          ih middleInventory populated allowed edgeResult.1 tailResident tailSafe nextValid index output
            (by simpa using selected)
        exact ⟨original, start, rowMiddle, rowValues, rowHeap, startInventory, rowInventory,
          rowMemos, rowFinal, actualChildren, by simpa using sourceIndex, actualReads, startValid, actualBuilt, symbol, guard, exactChildren,
          startReady, middleReady, startGrowth, middleGrowth, heapGrowth⟩
  exact RowsReads.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun {record originals entries edges before results after} _ memos _ _ =>
      RowsLaw formulas solver base record originals entries edges before results after memos)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    @nilCase (by intros; apply consCase <;> assumption) reads

/-- An actual raw row retains its indexed source, full fields, and growing call heaps. -/
theorem rows_indexed {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated (.editBelow entries))
    (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (resident : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos)
    {index : Nat} {result : EdgeValue Symbol Guard} (selected : results[index]? = some result) :
    ∃ original : EdgeValue Symbol Guard, ∃ start middle : SharedState width, ∃ values heap startInventory middleInventory rowMemos rowFinal,
    ∃ call : EditChildren record originals entries 0 original.children start values middle,
      edges[index]? = some original ∧
      ChildrenReads formulas solver base call rowMemos rowFinal ∧
      Valid start.checked.native.machine.heap rowMemos ∧
      run (makeEdge original.entry.key.symbol original.entry.key.constraint values)
        middle.checked.native.machine.heap = (result, heap) ∧
      result.entry.key.symbol = original.entry.key.symbol ∧
      result.entry.key.constraint = original.entry.key.constraint ∧ result.children = values ∧
      Ready formulas solver startInventory record originals base start ∧
      Ready formulas solver middleInventory record originals base middle ∧
      Grows start.checked.native.machine.heap after.checked.native.machine.heap ∧
      Grows middle.checked.native.machine.heap after.checked.native.machine.heap ∧
      Grows heap after.checked.native.machine.heap :=
  rows_law reads inventory populated allowed ready resident safe valid index result selected

/-- Every normalized output row retains an indexed raw source and its actual child reads. -/
theorem node_survivor {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries edges before rebuilt middle memos final value heap}
    {actual : EditRows (width := width) record originals entries edges before rebuilt middle}
    (reads : RowsReads formulas solver base actual memos final)
    (built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap))
    (inventory : Inventory) (populated : Populated (.editBelow entries))
    (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (resident : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos)
    {row : EdgeValue Symbol Guard} (selected : row ∈ SourceEqualityRequiredGraph.nodeEdges value) :
    ∃ index, ∃ original : EdgeValue Symbol Guard, ∃ start rowMiddle : SharedState width,
    ∃ values rowHeap startInventory middleInventory rowMemos rowFinal,
    ∃ call : EditChildren record originals entries 0 original.children start values rowMiddle,
      rebuilt[index]? = some row ∧ edges[index]? = some original ∧
      ChildrenReads formulas solver base call rowMemos rowFinal ∧
      Valid start.checked.native.machine.heap rowMemos ∧
      run (makeEdge original.entry.key.symbol original.entry.key.constraint values)
        rowMiddle.checked.native.machine.heap = (row, rowHeap) ∧
      row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children = values ∧
      Ready formulas solver startInventory record originals base start ∧
      Ready formulas solver middleInventory record originals base rowMiddle ∧
      Grows start.checked.native.machine.heap heap ∧
      Grows rowMiddle.checked.native.machine.heap heap ∧ Grows rowHeap heap ∧
      EqualityLeafProjectionPhysical.dead row = false := by
  obtain ⟨next, rows⟩ := rows_effects reads populated allowed ready resident safe valid
  have facts := rows.ready.checked.semantic.ready.semantic.1.normal.facts
  have normalized : row ∈ canonicalEdges (surviving rebuilt) := by
    have exactRows := EqualityLeafProjectionPhysical.makeNode_edges rebuilt middle.checked.native.machine.heap
      facts.coherent facts.linked rows.available
    simpa only [built] using exactRows ▸ selected
  have raw := (EqualityLeafProjectionPhysical.normalized_member middle.checked.native.machine.heap
    facts.coherent rebuilt rows.available row).mp normalized
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp raw.1
  obtain ⟨original, start, rowMiddle, values, rowHeap, startInventory, middleInventory,
    rowMemos, rowFinal, call, sourceIndex, childReads, startValid, edgeBuilt, symbol, guard, children,
    startReady, middleReady, startGrowth, middleGrowth, heapGrowth⟩ :=
    rows_indexed reads inventory populated allowed ready resident safe valid found
  have physical := node_physical rows.ready rebuilt rows.available
  have growth : Grows middle.checked.native.machine.heap heap := by
    simpa only [built] using physical.2.1.keeps.growth
  exact ⟨index, original, start, rowMiddle, values, rowHeap, startInventory, middleInventory,
    rowMemos, rowFinal, call, found, sourceIndex, childReads, startValid, edgeBuilt, symbol, guard,
    children, startReady, middleReady, grows_trans _ _ _ startGrowth growth,
    grows_trans _ _ _ middleGrowth growth, grows_trans _ _ _ heapGrowth growth, raw.2⟩

end MicroCFTA.SourceCurrentSharedEditRowLineage
