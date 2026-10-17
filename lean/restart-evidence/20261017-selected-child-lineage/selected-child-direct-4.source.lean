import MicroCFTA.SourceCurrentParentRowWriterLineage

/-!
# Exact selected-child prefixes in actual shared edits

An indexed child retains its actual preceding and following executions.
Selected children retain their node read receipt. Initial physical facts
and native history derive the captured states and their growth. This law
does not establish future completion or active outer-owner exclusion.
-/
namespace MicroCFTA.SourceCurrentSharedEditChildLineage
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- One source position retains the actual prefix, dispatch, suffix, and memo bundles. -/
def Slice (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat)
    (values : List (Value Symbol Guard)) (before : SharedState width)
    (results : List (Value Symbol Guard)) (after : SharedState width)
    (memos final : Memos) (index : Nat) (result : Value Symbol Guard) : Prop :=
  ∃ original : Value Symbol Guard, ∃ start finish : SharedState width, ∃ current saved : Memos,
  ∃ earlier : EditChildren record originals entries offset (values.take index) before (results.take index) start,
  ∃ later : EditChildren record originals entries (offset + index + 1)
      (values.drop (index + 1)) finish (results.drop (index + 1)) after,
    values[index]? = some original ∧
    ChildrenReads formulas solver base earlier memos current ∧
    ChildrenReads formulas solver base later saved final ∧
    ((SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = none ∧
      result = original ∧ finish = start ∧ saved = current) ∨
      ∃ edits, ∃ call : EditNode record originals edits original start result finish,
        SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = some edits ∧
        NodeReads formulas solver base call current saved)

/-- Actual child reads decompose at the same indexed input and output position. -/
theorem indexed {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    {index : Nat} {result : Value Symbol Guard} (selected : results[index]? = some result) :
    Slice formulas solver base record originals entries offset values before results after memos final index result := by
  have law : ∀ {record originals entries offset values before results after memos final}
      {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenReads formulas solver base actual memos final → ∀ index result,
        results[index]? = some result →
        Slice formulas solver base record originals entries offset values before results after memos final index result := by
    intro record originals entries offset values before results after memos final actual read
    exact ChildrenReads.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ∀ index result, results[index]? = some result →
          Slice formulas solver base record originals entries offset values before results after memos final index result)
      (motive_3 := fun _ _ _ _ => True)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
      (by
        intro record originals entries offset state memos index result selected
        simp at selected)
      (by
        intro record originals memos saved entries values before results after value offset absent rest read ih index result selected
        cases index with
        | zero =>
            have same : value = result := by simpa using selected
            exact ⟨value, before, before, memos, memos, .nil, rest, rfl, .nil, read,
              Or.inl ⟨by simpa using absent, same.symm, rfl, rfl⟩⟩
        | succ index =>
            obtain ⟨original, start, finish, current, saved, earlier, later, sourceIndex, firstRead, lastRead, dispatch⟩ :=
              ih index result (by simpa using selected)
            have combined : EditChildren record originals entries offset
                ((value :: values).take (index + 1)) before ((value :: results).take (index + 1)) start := by
              simpa only [List.take_succ_cons] using EditChildren.unselected offset absent earlier
            have combinedRead : ChildrenReads formulas solver base combined memos current := by
              simpa only [List.take_succ_cons] using ChildrenReads.unselected (absent := absent) firstRead
            refine ⟨original, start, finish, current, saved, combined, ?_, ?_, combinedRead, ?_, ?_⟩
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later
            · simpa using sourceIndex
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastRead
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatch)
      (by
        intro record originals memos current saved entries edits value before result middle values results after offset found first rest firstRead restRead _ ih index output selected
        cases index with
        | zero =>
            have same : result = output := by simpa using selected
            subst output
            exact ⟨value, before, middle, memos, current, .nil, rest, rfl, .nil, restRead,
              Or.inr ⟨edits, first, by simpa using found, firstRead⟩⟩
        | succ index =>
            obtain ⟨original, start, finish, currentMemos, savedMemos, earlier, later, sourceIndex,
              prefixRead, suffixRead, dispatch⟩ := ih index output (by simpa using selected)
            have combined : EditChildren record originals entries offset
                ((value :: values).take (index + 1)) before ((result :: results).take (index + 1)) start := by
              simpa only [List.take_succ_cons] using EditChildren.selected offset found first earlier
            have combinedRead : ChildrenReads formulas solver base combined memos currentMemos := by
              simpa only [List.take_succ_cons] using ChildrenReads.selected (found := found) firstRead prefixRead
            refine ⟨original, start, finish, currentMemos, savedMemos, combined, ?_, ?_, combinedRead, ?_, ?_⟩
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later
            · simpa using sourceIndex
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suffixRead
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatch)
      (by intros; trivial) (by intros; trivial) read
  exact law reads index result selected

end

private theorem safe_take {entries : List (Int × Edits Action)} {offset : Nat}
    {values : List (Value Symbol Guard)} (safe : ChildrenSafe entries offset values) (count : Nat) :
    ChildrenSafe entries offset (values.take count) := by
  intro index edits found original selected
  apply safe index edits found original
  by_cases bound : index < count
  · simpa only [List.getElem?_take, ite_eq_left bound] using selected
  · simp only [List.getElem?_take, ite_eq_right bound] at selected
    cases selected


private theorem safe_drop {entries : List (Int × Edits Action)} {offset : Nat}
    {values : List (Value Symbol Guard)} (safe : ChildrenSafe entries offset values) (count : Nat) :
    ChildrenSafe entries (offset + count) (values.drop count) := by
  intro index edits found original selected
  exact safe (count + index) edits (by simpa [Nat.add_assoc] using found) original
    (by simpa only [List.getElem?_drop] using selected)

section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A selected call derives its captured readiness, native histories, and chronological growth. -/
theorem selected {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated (.editBelow entries))
    (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (history : History before.checked)
    {index : Nat} {result : Value Symbol Guard} {edits : Edits EqualityNormalize.Path}
    (output : results[index]? = some result)
    (found : SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = some edits) :
    ∃ original : Value Symbol Guard, ∃ start finish : SharedState width,
    ∃ current saved : Memos, ∃ startInventory finishInventory : Inventory,
    ∃ earlier : EditChildren record originals entries offset (values.take index) before (results.take index) start,
    ∃ call : EditNode record originals edits original start result finish,
    ∃ later : EditChildren record originals entries (offset + index + 1)
        (values.drop (index + 1)) finish (results.drop (index + 1)) after,
      values[index]? = some original ∧
      ChildrenReads formulas solver base earlier memos current ∧
      NodeReads formulas solver base call current saved ∧
      ChildrenReads formulas solver base later saved final ∧
      Ready formulas solver startInventory record originals base start ∧
      Ready formulas solver finishInventory record originals base finish ∧
      History start.checked ∧ History finish.checked ∧
      Grows before.checked.native.machine.heap start.checked.native.machine.heap ∧
      Grows start.checked.native.machine.heap finish.checked.native.machine.heap ∧
      Grows finish.checked.native.machine.heap after.checked.native.machine.heap := by
  obtain ⟨original, start, finish, current, saved, earlier, later, sourceIndex, prefixRead, suffixRead, dispatch⟩ :=
    indexed reads output
  rcases dispatch with unused | ⟨chosen, call, chosenFound, callRead⟩
  · rw [found] at unused
    cases unused.1
  · have same : chosen = edits := Option.some.inj (chosenFound.symm.trans found)
    subst chosen
    have prefixAvailable : Values before.checked.native.machine.heap (values.take index) :=
      fun child member => available child (List.mem_of_mem_take member)
    obtain ⟨startInventory, prefixResult⟩ := children_effects prefixRead populated allowed ready prefixAvailable
      (safe_take safe index) valid
    have originalAvailable := prefixResult.effects.keeps.available original
      (available original (List.mem_of_getElem? sourceIndex))
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childFacts := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by
      rw [Allowed, SourceEqualityEdits.All] at allowed
      exact allowed _ _ member
    obtain ⟨finishInventory, called⟩ := node_effects callRead childFacts.1 childFacts.2 childAllowed prefixResult.ready
      originalAvailable (safe index edits found original sourceIndex) prefixResult.globals.valid
    have suffixAvailable : Values finish.checked.native.machine.heap (values.drop (index + 1)) := by
      intro child included
      exact called.effects.keeps.available child (prefixResult.effects.keeps.available child
        (available child (List.mem_of_mem_drop included)))
    have suffixSafe : ChildrenSafe entries (offset + index + 1) (values.drop (index + 1)) := by
      simpa [Nat.add_assoc] using safe_drop safe (index + 1)
    obtain ⟨next, suffixResult⟩ := children_effects suffixRead populated allowed called.ready suffixAvailable suffixSafe called.globals.valid
    have startHistory := SourceCurrentParentNativeHistory.edit_children prefixRead history
      ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid
    have finishHistory := SourceCurrentParentNativeHistory.edit_node callRead startHistory.1 startHistory.2
    exact ⟨original, start, finish, current, saved, startInventory, finishInventory, earlier, call, later,
      sourceIndex, prefixRead, callRead, suffixRead, prefixResult.ready, called.ready, startHistory.1, finishHistory.1,
      prefixResult.effects.keeps.growth, called.effects.keeps.growth, suffixResult.effects.keeps.growth⟩

end

end MicroCFTA.SourceCurrentSharedEditChildLineage
