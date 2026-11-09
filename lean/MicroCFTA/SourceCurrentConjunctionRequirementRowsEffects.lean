import MicroCFTA.SourceCurrentConjunctionRequirementRows
import MicroCFTA.SourceCurrentConjunctionRequirementCellsEffects

/-!
# Physical effects of shared requirement rows

Tuple preparation allocates equality values and unforced descriptors.
Resident edge records supply the captured child forests. No projection is
needed for these effects. Row traversal retains all pending cell operands
and every raw tuple in each remaining spine, including on failed outcomes.
The private heaps are not selected by the conjunction worklist here.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementCellsEffects (CellInputs Inputs)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "RowState" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- A pending raw row spine retains its actual canonical edge operands. -/
def RawInputs (heap : InternedConstructorTemplates.State Symbol Guard) : Spine Symbol Formula → Prop
  | .pending tuples => ∀ tuple ∈ tuples, Edges heap tuple
  | .done _ => True

/-- All unfinished raw spines have resident tuple edges at the current heap. -/
def SpineInputs (before : RowState) : Prop :=
  ∀ spine ∈ before.spines, RawInputs before.requirements.physical.heap spine

/-- Ordered descriptor allocation retains earlier inputs and the new pending forests. -/
theorem allocateCells_inputs (cells : List Cell) (before : Cells) (inputs : Inputs before)
    (added : ∀ cell ∈ cells, CellInputs before.physical.heap cell) :
    Inputs (allocateCells cells before).2 := by
  intro handle cell found
  have member : cell ∈ (allocateCells cells before).2.cells := List.mem_of_getElem? found
  rw [allocateCells_order] at member
  rw [allocateCells_physical]
  rcases List.mem_append.mp member with old | new
  · obtain ⟨index, present⟩ := List.mem_iff_getElem?.mp old
    exact inputs index cell present
  · exact added cell new

private theorem descriptors_inputs (tuple : List Row) (constraints : EqualityNormalize.Constraints)
    (before : RowState) (ready : Ready before.requirements.physical)
    (resident : Edges before.requirements.physical.heap tuple) :
    ∀ cell ∈ descriptors tuple constraints, CellInputs before.requirements.physical.heap cell := by
  intro cell member
  change cell ∈ (SourceCurrentConjunctionRequirements.columns tuple).map _ ++ constraints.map _ at member
  rcases List.mem_append.mp member with column | constraint
  · obtain ⟨nodes, _, same⟩ := List.mem_map.mp column
    cases same
    trivial
  · obtain ⟨paths, _, same⟩ := List.mem_map.mp constraint
    cases same
    intro job included
    obtain ⟨forest, forestIn, present⟩ := List.mem_flatMap.mp included
    obtain ⟨path, _, same⟩ := List.mem_map.mp present
    cases same
    obtain ⟨edge, edgeIn, same⟩ := List.mem_map.mp forestIn
    cases same
    exact ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge edgeIn)

/-- Actual tuple equality and descriptor allocation preserve effects and pending-cell inputs on every outcome. -/
theorem prepareTuple_effects (tuple : List Row) (before : RowState)
    (ready : Ready before.requirements.physical) (inputs : Inputs before.requirements)
    (resident : Edges before.requirements.physical.heap tuple) :
    Effects before.requirements.physical (prepareTuple tuple before).state.requirements.physical ∧
      Inputs (prepareTuple tuple before).state.requirements := by
  obtain ⟨result, done, valid, _, _, _, growth, fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.requirements.physical.heap
      before.requirements.physical.equality ready.valid ready.fields resident
  constructor
  · rw [prepareTuple_physical]
    exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready,
      ⟨ready.semantic, ready.costs, valid, fields⟩, growth⟩
  · have folded : SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality =
        (.ok (some result), (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2) :=
      Prod.ext done rfl
    cases classes : SourceEqualityInheritedPayload.classes result.payload with
    | none =>
        simp only [prepareTuple, done, classes, Outcome.state]
        exact inputs
    | some constraints =>
        rw [prepareTuple_live tuple before _ result constraints folded classes]
        exact allocateCells_inputs _ _ inputs (descriptors_inputs tuple constraints before ready resident)

private theorem spineInputs_prepare (tuple : List Row) (before : RowState) (inputs : SpineInputs before) :
    SpineInputs (prepareTuple tuple before).state := by
  intro spine member
  rw [prepareTuple_spines] at member
  change RawInputs (prepareTuple tuple before).state.requirements.physical.heap spine
  rw [prepareTuple_physical]
  exact inputs spine member

private theorem spineInputs_update (handle : Nat) (replacement : Spine Symbol Formula) (before : RowState)
    (inputs : SpineInputs before) (own : RawInputs before.requirements.physical.heap replacement) :
    SpineInputs (updateSpine handle replacement before) := by
  intro spine member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact inputs spine old
  · exact same.symm ▸ own

private theorem spineInputs_allocate (spine : Spine Symbol Formula) (before : RowState)
    (inputs : SpineInputs before) (own : RawInputs before.requirements.physical.heap spine) :
    SpineInputs (allocateSpine spine before).2 := by
  intro cell member
  rcases List.mem_append.mp member with old | new
  · exact inputs cell old
  · have same : cell = spine := List.mem_singleton.mp new
    exact same.symm ▸ own

private theorem nextRow_pending_effects (handle : Nat) (tuples : List (List Row)) (before : RowState)
    (ready : Ready before.requirements.physical) (inputs : Inputs before.requirements)
    (raw : SpineInputs before) (found : lookupSpine handle before = some (.pending tuples)) :
    Effects before.requirements.physical (nextRow handle before).state.requirements.physical ∧
      Inputs (nextRow handle before).state.requirements ∧ SpineInputs (nextRow handle before).state := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      exact ⟨Effects.refl _ ready, inputs, spineInputs_update handle (.done none) before raw trivial⟩
  | cons tuple rest ih =>
      have resident := raw (.pending (tuple :: rest)) (List.mem_of_getElem? found) tuple List.mem_cons_self
      have first := prepareTuple_effects tuple before ready inputs resident
      have retained := spineInputs_prepare tuple before raw
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          have kept : Effects before.requirements.physical after.requirements.physical ∧ Inputs after.requirements := by
            simpa only [prepared, Outcome.state] using first
          have remaining : SpineInputs after := by simpa only [prepared, Outcome.state] using retained
          exact ⟨kept.1, kept.2, remaining⟩
      | done row after =>
          have kept : Effects before.requirements.physical after.requirements.physical ∧ Inputs after.requirements := by
            simpa only [prepared, Outcome.state] using first
          have remaining : SpineInputs after := by simpa only [prepared, Outcome.state] using retained
          have spines := prepareTuple_spines tuple before
          rw [prepared] at spines
          change after.spines = before.spines at spines
          have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [spines]
            exact found
          have tailInputs : RawInputs after.requirements.physical.heap (.pending rest) := by
            intro next member
            exact remaining (.pending (tuple :: rest)) (List.mem_of_getElem? afterFound) next
              (List.mem_cons_of_mem _ member)
          cases row with
          | none =>
              rw [nextRow_rejected handle tuple rest before after found prepared]
              have nextRaw := spineInputs_update handle (.pending rest) after remaining tailInputs
              have nextFound := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after afterFound
              have last := ih (updateSpine handle (.pending rest) after) kept.1.ready kept.2 nextRaw nextFound
              exact ⟨kept.1.trans last.1, last.2⟩
          | some row =>
              rw [nextRow_live handle tuple rest before after row found prepared]
              exact ⟨kept.1, kept.2, spineInputs_update handle _ _
                (spineInputs_allocate (.pending rest) after remaining tailInputs) trivial⟩

/-- Actual finite row traversal retains full effects and all unfinished operands, including on faults. -/
theorem nextRow_effects (handle : Nat) (before : RowState)
    (ready : Ready before.requirements.physical) (inputs : Inputs before.requirements)
    (raw : SpineInputs before) :
    Effects before.requirements.physical (nextRow handle before).state.requirements.physical ∧
      Inputs (nextRow handle before).state.requirements ∧ SpineInputs (nextRow handle before).state := by
  cases found : lookupSpine handle before with
  | none =>
      rw [nextRow_missing handle before found]
      exact ⟨Effects.refl _ ready, inputs, raw⟩
  | some spine =>
      cases spine with
      | done row =>
          rw [nextRow_hit handle row before found]
          exact ⟨Effects.refl _ ready, inputs, raw⟩
      | pending tuples => exact nextRow_pending_effects handle tuples before ready inputs raw found

end MicroCFTA.SourceCurrentConjunctionRequirementRowsEffects
