import MicroCFTA.SourceCurrentConjunctionRequirementRowsValues
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes

/-!
# Resident row operands from a current semantic heap

Tuple preparation retains the value heap on every outcome. Resident tuple
edges supply the values of new columns and pending class forests. The
finite row traversal retains these values and all suspended raw operands.
No cost heap, equality readiness, or successful read is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsWeakValues
open InternedConstructorTemplates (EdgeValue)
open InternedNestedProvenance (Values Edges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementCellsValues (CellValues Invariant)
open SourceCurrentConjunctionRequirementRowsEffects (RawInputs SpineInputs)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- Current semantic edge records supply all literal descriptor operands. -/
theorem descriptors_values (tuple : List Row) (constraints : EqualityNormalize.Constraints)
    (before : Storage) (semantic : SemanticHeap before.requirements.physical.heap)
    (resident : Edges before.requirements.physical.heap tuple) :
    ∀ cell ∈ descriptors tuple constraints, CellValues before.requirements.physical.heap cell := by
  have forests : ∀ forest ∈ tuple.map EdgeValue.children, Values before.requirements.physical.heap forest := by
    intro forest member
    obtain ⟨edge, included, same⟩ := List.mem_map.mp member
    cases same
    exact semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge included)
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

/-- Actual tuple preparation retains current stored values without equality readiness. -/
theorem prepareTuple_values (tuple : List Row) (before : Storage)
    (semantic : SemanticHeap before.requirements.physical.heap)
    (values : Invariant before.requirements)
    (resident : Edges before.requirements.physical.heap tuple) :
    Invariant (prepareTuple tuple before).state.requirements := by
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
      exact SourceCurrentConjunctionRequirementRowsValues.allocateCells_values _ current values
        (descriptors_values tuple _ before semantic resident)

private theorem spines_same (before after : Storage) (same : after.spines = before.spines)
    (heap : after.requirements.physical.heap = before.requirements.physical.heap)
    (raw : SpineInputs before) : SpineInputs after := by
  intro spine member
  rw [same] at member
  change RawInputs after.requirements.physical.heap spine
  rw [heap]
  exact raw spine member

private theorem spines_update (handle : Nat) (replacement : Spine Symbol Formula) (before : Storage)
    (raw : SpineInputs before) (own : RawInputs before.requirements.physical.heap replacement) :
    SpineInputs (updateSpine handle replacement before) := by
  intro spine member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact raw spine old
  · exact same.symm ▸ own

private theorem spines_allocate (tuples : List (List Row)) (before : Storage)
    (raw : SpineInputs before) (own : RawInputs before.requirements.physical.heap (.pending tuples)) :
    SpineInputs (allocateSpine (.pending tuples) before).2 := by
  intro spine member
  rcases List.mem_append.mp member with old | fresh
  · exact raw spine old
  · have same : spine = .pending tuples := List.mem_singleton.mp fresh
    exact same.symm ▸ own

private theorem pending_values (handle : Nat) (tuples : List (List Row)) (before : Storage)
    (semantic : SemanticHeap before.requirements.physical.heap)
    (values : Invariant before.requirements) (raw : SpineInputs before)
    (found : lookupSpine handle before = some (.pending tuples)) :
    Invariant (nextRow handle before).state.requirements ∧ SpineInputs (nextRow handle before).state := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      exact ⟨values, spines_update handle (.done none) before raw True.intro⟩
  | cons tuple rest ih =>
      have resident := raw (.pending (tuple :: rest)) (List.mem_of_getElem? found) tuple List.mem_cons_self
      have first := prepareTuple_values tuple before semantic values resident
      have sameSpines := prepareTuple_spines tuple before
      have sameHeap := SourceCurrentConjunctionRequirementRowsProbes.prepareTuple_heap tuple before
      have retained := spines_same before (prepareTuple tuple before).state sameSpines sameHeap raw
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          simpa only [prepared, Outcome.state] using And.intro first retained
      | done row after =>
          have current : Invariant after.requirements ∧ SpineInputs after := by
            simpa only [prepared, Outcome.state] using And.intro first retained
          rw [prepared] at sameSpines sameHeap
          change after.spines = before.spines at sameSpines
          change after.requirements.physical.heap = before.requirements.physical.heap at sameHeap
          have afterSemantic : SemanticHeap after.requirements.physical.heap := by
            rw [sameHeap]
            exact semantic
          have present : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [sameSpines]
            exact found
          have suffix : RawInputs after.requirements.physical.heap (.pending rest) := by
            intro next member
            exact current.2 (.pending (tuple :: rest)) (List.mem_of_getElem? present) next
              (List.mem_cons_of_mem _ member)
          cases row with
          | none =>
              rw [nextRow_rejected handle tuple rest before after found prepared]
              exact ih (before := updateSpine handle (.pending rest) after) (semantic := afterSemantic)
                (values := current.1) (raw := spines_update handle (.pending rest) after current.2 suffix)
                (found := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after present)
          | some handles =>
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact ⟨current.1, spines_update handle (.done (some (handles, after.spines.length)))
                (allocateSpine (.pending rest) after).2 (spines_allocate rest after current.2 suffix) True.intro⟩

/-- Every actual row outcome retains stored values and all resident pending raw operands. -/
theorem nextRow_values (handle : Nat) (before : Storage)
    (semantic : SemanticHeap before.requirements.physical.heap)
    (values : Invariant before.requirements) (raw : SpineInputs before) :
    Invariant (nextRow handle before).state.requirements ∧ SpineInputs (nextRow handle before).state := by
  cases found : lookupSpine handle before with
  | none =>
      rw [nextRow_missing handle before found]
      exact ⟨values, raw⟩
  | some spine =>
      cases spine with
      | done row =>
          rw [nextRow_hit handle row before found]
          exact ⟨values, raw⟩
      | pending tuples => exact pending_values handle tuples before semantic values raw found

end MicroCFTA.SourceCurrentConjunctionRequirementRowsWeakValues
