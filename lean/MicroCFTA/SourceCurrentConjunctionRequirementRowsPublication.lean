import MicroCFTA.SourceCurrentConjunctionRequirementRowsRejectionSoundness
import MicroCFTA.SourceCurrentConjunctionRequirementRowsRefinement
import MicroCFTA.SourceCurrentConjunctionRequirementRowsClosed
import MicroCFTA.SourceCurrentConjunctionRequirementPublication

/-!
# Coupled row publication and descriptor origins

One actual row observation retains its original raw suffix and cell origins.
Rejected tuples allocate no cells. The first live tuple supplies one literal
descriptor batch at the original cell offset. The returned heap preserves
that same extended origin list, exact descriptor lookups, and the fresh tail.
Faults retain their actual operational trace. This component does not prove
whole-table semantic coverage or Boolean soundness.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsPublication
open InternedConstructorTemplates (EdgeValue)
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementRowsTrace (Rejected Finish Trace)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Tuple" => List (EdgeValue Symbol Guard)
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Observation" => Outcome Symbol Formula (Option (Handles × Nat))
local notation "Refined" => SourceCurrentConjunctionRequirementCellsRefinement.Invariant
local notation "combined" => SourceCurrentConjunctionEmptinessRows.combined
local notation "edgeView" => SourceCurrentConjunctionEquality.edgeView

/-- Publication retains one selected source tuple and one exact descriptor-origin extension. -/
def Published (handle : Nat) (before : Storage) (origins : List Cell) (original : List Tuple) : Observation → Prop
  | .failed _ _ => True
  | .done none after =>
      (∀ tuple ∈ original, combined (tuple.map edgeView) = none) ∧
      Refined origins after.requirements ∧ after.requirements.cells = before.requirements.cells ∧
      Ready after.requirements.physical ∧ after.spines.length = before.spines.length
  | .done (some (handles, tail)) after =>
      ∃ skipped chosen rest current prepared operations result constraints,
        original = skipped ++ chosen :: rest ∧
        (∀ tuple ∈ skipped, combined (tuple.map edgeView) = none) ∧
        prepareTuple chosen current = .done (some handles) prepared ∧
        SourceCurrentConjunctionEquality.fold chosen current.requirements.physical.equality =
          (.ok (some result), operations) ∧
        SourceEqualityInheritedPayload.classes result.payload = some constraints ∧
        combined (chosen.map edgeView) = some constraints ∧
        handles = List.range' before.requirements.cells.length (descriptors chosen constraints).length ∧
        Refined (origins ++ descriptors chosen constraints) after.requirements ∧
        after.requirements.cells = before.requirements.cells ++ descriptors chosen constraints ∧
        (∀ index cell, (descriptors chosen constraints)[index]? = some cell →
          handles[index]? = some (before.requirements.cells.length + index) ∧
          (origins ++ descriptors chosen constraints)[before.requirements.cells.length + index]? = some cell) ∧
        tail = before.spines.length ∧
        lookupSpine tail after = some (.pending rest) ∧
        lookupSpine handle after = some (.done (some (handles, tail))) ∧
        (∀ cell ∈ descriptors chosen constraints, SourceCurrentConjunctionRequirementCellsClosed.CellClosed cell) ∧
        Ready after.requirements.physical ∧ after.spines.length = before.spines.length + 1

private theorem same_cells {origins : List Cell} {before after : Cells}
    (refined : Refined origins before) (same : after.cells = before.cells) : Refined origins after := by
  refine ⟨refined.length.trans (congrArg List.length same).symm, ?_⟩
  intro handle original current originFound currentFound
  apply refined.cells handle original current originFound
  simpa only [SourceCurrentConjunctionRequirementCells.lookup, same] using currentFound

private theorem rejected_frame {handle : Nat} {original remaining : List Tuple} {before after : Storage}
    (actual : Rejected handle original before remaining after)
    (found : lookupSpine handle before = some (.pending original)) :
    after.requirements.cells = before.requirements.cells ∧ after.spines.length = before.spines.length ∧
      lookupSpine handle after = some (.pending remaining) := by
  revert found
  induction actual with
  | refl => intro found; exact ⟨rfl, rfl, found⟩
  | @step tuple rest remaining before current after prepared tail ih =>
      intro found
      obtain ⟨_, _, currentEq⟩ := SourceCurrentConjunctionRequirementRowsTrace.prepareTuple_none prepared
      have present : lookupSpine handle current = some (.pending (tuple :: rest)) := by
        rw [currentEq]
        exact found
      have frame := ih (lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) current present)
      refine ⟨frame.1.trans ?_, ?_, frame.2.2⟩
      · rw [currentEq]
        rfl
      · calc
          after.spines.length = current.spines.length := by
            simpa only [updateSpine, List.length_set] using frame.2.1
          _ = before.spines.length := by rw [currentEq]

private theorem pending_publication {handle : Nat} {original remaining : List Tuple}
    {before current : Storage} {origins : List Cell} {outcome : Observation}
    (found : lookupSpine handle before = some (.pending original))
    (rejected : Rejected handle original before remaining current) (finished : Finish handle remaining current outcome)
    (ready : Ready before.requirements.physical)
    (resident : ∀ tuple ∈ original, Edges before.requirements.physical.heap tuple)
    (closed : ∀ tuple ∈ original, ClosedEdges tuple) (refined : Refined origins before.requirements) :
    Published handle before origins original outcome := by
  obtain ⟨skipped, split, contradictions, currentReady, sameHeap⟩ :=
    SourceCurrentConjunctionRequirementRowsRejectionSoundness.rejected_prefix rejected ready resident
  have frame := rejected_frame rejected found
  have currentRefined := same_cells refined frame.1
  cases finished with
  | exhausted =>
      have all : ∀ tuple ∈ original, combined (tuple.map edgeView) = none := by
        have same : original = skipped := by simpa only [List.append_nil] using split
        simpa only [same] using contradictions
      refine ⟨all, currentRefined, frame.1, currentReady, ?_⟩
      simpa only [updateSpine, List.length_set] using frame.2.1
  | failed prepared => trivial
  | @live chosen rest current prepared handles actual =>
      have chosenIn : chosen ∈ original := by
        rw [split]
        exact List.mem_append_right _ List.mem_cons_self
      have chosenResident : Edges current.requirements.physical.heap chosen := by
        rw [sameHeap]
        exact resident chosen chosenIn
      obtain ⟨operations, result, constraints, folded, classes, sameHandles, preparedEq⟩ :=
        SourceCurrentConjunctionRequirementRowsTrace.prepareTuple_some actual
      let foldCells : Cells := {current.requirements with
        physical := ⟨current.requirements.physical.heap, operations⟩}
      have foldRefined : Refined origins foldCells := same_cells currentRefined rfl
      have allocatedRefined := SourceCurrentConjunctionRequirementRowsRefinement.allocateCells_refinement
        (descriptors chosen constraints) foldCells origins foldRefined
      have selectedRefined : Refined (origins ++ descriptors chosen constraints) prepared.requirements := by
        rw [preparedEq]
        exact allocatedRefined
      have range : handles = List.range' before.requirements.cells.length (descriptors chosen constraints).length := by
        rw [sameHandles, allocateCells_handles]
        change List.range' current.requirements.cells.length _ = _
        rw [frame.1]
      have appended : prepared.requirements.cells = before.requirements.cells ++ descriptors chosen constraints := by
        rw [preparedEq, allocateCells_order]
        change current.requirements.cells ++ descriptors chosen constraints = _
        rw [frame.1]
      obtain ⟨checked, done, valid, _, checkedClasses, _, _, fields⟩ :=
        SourceCurrentConjunctionEquality.fold_heap_correct chosen current.requirements.physical.heap
          current.requirements.physical.equality currentReady.valid currentReady.fields chosenResident
      have sameResult : checked = result :=
        Option.some.inj (Except.ok.inj (done.symm.trans (congrArg Prod.fst folded)))
      subst checked
      have combinedLive : combined (chosen.map edgeView) = some constraints := checkedClasses.symm.trans classes
      have physical := prepareTuple_physical chosen current
      rw [actual] at physical
      change prepared.requirements.physical =
        ⟨current.requirements.physical.heap,
          (SourceCurrentConjunctionEquality.fold chosen current.requirements.physical.equality).2⟩ at physical
      have selectedReady : Ready prepared.requirements.physical := by
        rw [physical]
        exact ⟨currentReady.semantic, currentReady.costs, valid, fields⟩
      have spines := prepareTuple_spines chosen current
      rw [actual] at spines
      change prepared.spines = current.spines at spines
      have tailEq : prepared.spines.length = before.spines.length :=
        (congrArg List.length spines).trans frame.2.1
      have tailPresent := (nextRow_live_tail handle chosen rest current prepared handles frame.2.2 actual).1
      have published := SourceCurrentConjunctionRequirementPublication.nextRow_done handle current _
        (some (handles, prepared.spines.length)) (nextRow_live handle chosen rest current prepared handles frame.2.2 actual)
      refine ⟨skipped, chosen, rest, current, prepared, operations, result, constraints, split, contradictions,
        actual, folded, classes, combinedLive, range, selectedRefined, appended, ?_, tailEq, tailPresent, published,
        SourceCurrentConjunctionRequirementRowsClosed.descriptors_closed chosen constraints (closed chosen chosenIn),
        selectedReady, ?_⟩
      · intro index cell descriptor
        have registered := SourceCurrentConjunctionRequirementRowsRefinement.allocateCells_origin
          (descriptors chosen constraints) foldCells origins foldRefined index cell descriptor
        constructor
        · rw [sameHandles]
          simpa only [foldCells, frame.1] using registered.1
        · simpa only [foldCells, frame.1] using registered.2
      · simp only [updateSpine, allocateSpine, List.length_set, List.length_append,
          List.length_singleton, tailEq]

/-- Actual pending-row publication derives one coupled trace and origin certificate without a future result premise. -/
theorem nextRow_publication (handle : Nat) (before : Storage) (origins : List Cell) (original : List Tuple)
    (found : lookupSpine handle before = some (.pending original)) (ready : Ready before.requirements.physical)
    (resident : ∀ tuple ∈ original, Edges before.requirements.physical.heap tuple)
    (closed : ∀ tuple ∈ original, ClosedEdges tuple) (refined : Refined origins before.requirements) :
    Trace handle before (nextRow handle before) ∧ Published handle before origins original (nextRow handle before) := by
  have actual := SourceCurrentConjunctionRequirementRowsTrace.nextRow_trace handle before
  refine ⟨actual, ?_⟩
  generalize computed : nextRow handle before = outcome at actual ⊢
  cases actual with
  | missing absent => rw [found] at absent; cases absent
  | cached cached => rw [found] at cached; cases cached
  | pending observed rejected finished =>
      have same := Spine.pending.inj (Option.some.inj (observed.symm.trans found))
      cases same
      exact pending_publication found rejected finished ready resident closed refined

end MicroCFTA.SourceCurrentConjunctionRequirementRowsPublication
