import MicroCFTA.SourceCurrentConjunctionRequirementRowsEffects
import MicroCFTA.SourceCurrentConjunctionRequirementCellsValues

/-!
# Resident values in shared requirement rows

Actual equality folds retain the native heap. Descriptor allocation stores
resident columns and empty collected prefixes. Finite row traversal preserves
all stored cell values on successful and failed outcomes. The weak physical
effects and raw-spine proofs remain unchanged. No projection is forced here.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsValues
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Physical)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementCellsValues (CellValues Invariant)
open SourceCurrentConjunctionRequirementRowsEffects (RawInputs SpineInputs)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- Resident stored values supply the weaker current pending-job inputs. -/
theorem cells_inputs (before : Cells) (values : Invariant before) :
    SourceCurrentConjunctionRequirementCellsEffects.Inputs before := by
  intro handle cell found
  cases cell with
  | column nodes | done nodes => trivial
  | pending cursor => exact (values handle _ found).2

/-- Actual native growth retains cached values when only the physical cell state changes. -/
theorem cells_grows (before : Cells) (after : Physical Symbol Formula)
    (kept : SourceEqualityRequiredCache.Keeps before.physical.heap after.heap) (values : Invariant before) :
    Invariant {before with physical := after} := by
  intro handle cell found
  have own := values handle cell found
  cases cell with
  | column nodes | done nodes =>
      intro node member
      exact kept.available node (own node member)
  | pending cursor =>
      constructor
      · intro node member
        exact kept.available node (own.1 node member)
      · intro job member node included
        exact kept.available node (own.2 job member node included)

/-- Actual native growth retains every raw tuple when the spine list is unchanged. -/
theorem spines_grows (before after : Storage)
    (kept : SourceEqualityRequiredCache.Keeps before.requirements.physical.heap after.requirements.physical.heap)
    (same : after.spines = before.spines) (raw : SpineInputs before) : SpineInputs after := by
  intro spine member
  rw [same] at member
  have own := raw spine member
  cases spine with
  | done row => trivial
  | pending tuples =>
      intro tuple included edge present
      exact InternedEdgeResidency.edge_grows _ _ kept.growth edge (own tuple included edge present)

/-- Allocating ordered descriptors preserves all earlier values and their new resident operands. -/
theorem allocateCells_values (cells : List Cell) (before : Cells) (values : Invariant before)
    (added : ∀ cell ∈ cells, CellValues before.physical.heap cell) :
    Invariant (allocateCells cells before).2 := by
  induction cells generalizing before with
  | nil => exact values
  | cons cell rest ih =>
      change Invariant (allocateCells rest (SourceCurrentConjunctionRequirementCells.allocate cell before).2).2
      exact ih _ (SourceCurrentConjunctionRequirementCellsValues.allocate_values cell before values
        (added cell List.mem_cons_self))
        (fun later member => added later (List.mem_cons_of_mem _ member))

/-- Canonical resident tuple edges supply every literal column and pending class descriptor. -/
theorem descriptors_values (tuple : List Row) (constraints : EqualityNormalize.Constraints) (before : Storage)
    (ready : Ready before.requirements.physical) (resident : Edges before.requirements.physical.heap tuple) :
    ∀ cell ∈ descriptors tuple constraints, CellValues before.requirements.physical.heap cell := by
  have forests : ∀ forest ∈ tuple.map EdgeValue.children, Values before.requirements.physical.heap forest := by
    intro forest member
    obtain ⟨edge, included, same⟩ := List.mem_map.mp member
    cases same
    exact ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge included)
  intro cell member
  change cell ∈ (SourceCurrentConjunctionRequirements.columns tuple).map _ ++ constraints.map _ at member
  rcases List.mem_append.mp member with column | constraint
  · obtain ⟨nodes, included, same⟩ := List.mem_map.mp column
    cases same
    intro node member
    obtain ⟨forest, forestIn, childIn⟩ := MergedPhysicalGroupEdges.columns_member _ _ nodes included node member
    exact forests forest forestIn node childIn
  · obtain ⟨paths, _, same⟩ := List.mem_map.mp constraint
    cases same
    constructor
    · intro node member
      cases member
    · intro job included
      obtain ⟨forest, forestIn, present⟩ := List.mem_flatMap.mp included
      obtain ⟨path, _, same⟩ := List.mem_map.mp present
      cases same
      exact forests forest forestIn

/-- Every actual tuple preparation retains physical effects and the complete stored-value invariant. -/
theorem prepareTuple_values (tuple : List Row) (before : Storage)
    (ready : Ready before.requirements.physical) (values : Invariant before.requirements)
    (resident : Edges before.requirements.physical.heap tuple) :
    Effects before.requirements.physical (prepareTuple tuple before).state.requirements.physical ∧
      Invariant (prepareTuple tuple before).state.requirements := by
  have kept := SourceCurrentConjunctionRequirementRowsEffects.prepareTuple_effects tuple before ready
    (cells_inputs before.requirements values) resident
  refine ⟨kept.1, ?_⟩
  unfold prepareTuple
  dsimp only
  split
  · exact values
  · exact values
  · split
    · exact values
    · let current : Cells := {before.requirements with physical :=
        ⟨before.requirements.physical.heap,
          (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩}
      exact allocateCells_values _ current values (descriptors_values tuple _ before ready resident)

private theorem raw_update (target : Nat) (tuples : List (List Row)) (before : Storage)
    (raw : SpineInputs before) (own : RawInputs before.requirements.physical.heap (.pending tuples)) :
    SpineInputs (updateSpine target (.pending tuples) before) := by
  intro spine member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact raw spine old
  · exact same.symm ▸ own

private theorem pending_values (handle : Nat) (tuples : List (List Row)) (before : Storage)
    (ready : Ready before.requirements.physical) (values : Invariant before.requirements)
    (raw : SpineInputs before) (found : lookupSpine handle before = some (.pending tuples)) :
    Invariant (nextRow handle before).state.requirements := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      exact values
  | cons tuple rest ih =>
      have resident := raw (.pending (tuple :: rest)) (List.mem_of_getElem? found) tuple List.mem_cons_self
      have first := prepareTuple_values tuple before ready values resident
      have spines := prepareTuple_spines tuple before
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          simpa only [prepared, Outcome.state] using first.2
      | done row after =>
          have current : Effects before.requirements.physical after.requirements.physical ∧ Invariant after.requirements := by
            simpa only [prepared, Outcome.state] using first
          rw [prepared] at spines
          change after.spines = before.spines at spines
          have remaining := spines_grows before after current.1.keeps spines raw
          have present : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [spines]
            exact found
          cases row with
          | none =>
              rw [nextRow_rejected handle tuple rest before after found prepared]
              have suffix : RawInputs after.requirements.physical.heap (.pending rest) := by
                intro next member
                exact remaining (.pending (tuple :: rest)) (List.mem_of_getElem? present) next
                  (List.mem_cons_of_mem _ member)
              exact ih (updateSpine handle (.pending rest) after) current.1.ready current.2
                (raw_update handle rest after remaining suffix)
                (lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after present)
          | some handles =>
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact current.2

/-- Every finite row outcome preserves resident cell values and all actual pending raw operands. -/
theorem nextRow_values (handle : Nat) (before : Storage)
    (ready : Ready before.requirements.physical) (values : Invariant before.requirements)
    (raw : SpineInputs before) :
    Effects before.requirements.physical (nextRow handle before).state.requirements.physical ∧
      Invariant (nextRow handle before).state.requirements ∧ SpineInputs (nextRow handle before).state := by
  have kept := SourceCurrentConjunctionRequirementRowsEffects.nextRow_effects handle before ready
    (cells_inputs before.requirements values) raw
  refine ⟨kept.1, ?_, kept.2.2⟩
  cases found : lookupSpine handle before with
  | none =>
      rw [nextRow_missing handle before found]
      exact values
  | some spine =>
      cases spine with
      | done row =>
          rw [nextRow_hit handle row before found]
          exact values
      | pending tuples => exact pending_values handle tuples before ready values raw found

end MicroCFTA.SourceCurrentConjunctionRequirementRowsValues
