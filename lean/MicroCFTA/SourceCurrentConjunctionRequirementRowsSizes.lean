import MicroCFTA.SourceCurrentConjunctionRequirementCellsNumeric
import MicroCFTA.SourceCurrentConjunctionRequirementRows
import MicroCFTA.SourceCurrentConjunctionTupleBounds
import MicroCFTA.SourceCurrentConjunctionRequirementNumeric
import MicroCFTA.SourceCurrentConjunctionGuardUniverse

/-!
# Quantitative profiles of actual shared row descriptors

Literal tuples and classes determine descriptor counts and pending job
profiles. Actual equality readiness derives the classes used by allocation.
Resident payload mass bounds child widths. Current physical records supply
their own guard carrier. No future normalized classes or projections are
required. The equality fold does not change the value heap.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsSizes
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionTupleBounds (shapeThrough)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- A fresh descriptor retains its literal column width or pending job profile. -/
def Profile (count width shape : Nat) : Cell → Prop
  | .column nodes => nodes.length ≤ count
  | .pending cursor => cursor.collected = [] ∧ cursor.pending.length ≤ count * shape ∧
      SourceCurrentConjunctionRequirementCellsNumeric.depth cursor.pending ≤ shape ∧
      SourceCurrentConjunctionRequirementCellsNumeric.width cursor.pending ≤ width
  | .done _ => False

/-- Actual allocation appends one bounded batch and registers the same returned handles. -/
def Allocation (count width shape : Nat) (before : Storage) (row : Option Handles) (after : Storage) : Prop :=
  ∃ added : List Cell,
    after.requirements.cells = before.requirements.cells ++ added ∧ added.length ≤ width + shape ∧
    (∀ cell ∈ added, Profile count width shape cell) ∧
    (∀ handles, row = some handles → handles = List.range' before.requirements.cells.length added.length) ∧
    ∀ handles, row = some handles → ∀ handle ∈ handles,
      ∃ cell, SourceCurrentConjunctionRequirementCells.lookup handle after.requirements = some cell ∧
        Profile count width shape cell

private theorem fold_max_le (measure : A → Nat) (items : List A) (bound : Nat)
    (limits : ∀ item ∈ items, measure item ≤ bound) :
    items.foldr (fun item previous => max (measure item) previous) 0 ≤ bound := by
  induction items with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
      exact Nat.max_le.mpr ⟨limits first List.mem_cons_self,
        ih (fun item member => limits item (List.mem_cons_of_mem _ member))⟩

private theorem arity_le (tuple : List Row) (width : Nat)
    (widths : ∀ edge ∈ tuple, edge.children.length ≤ width) :
    SourceCurrentConjunctionRequirements.arity tuple ≤ width := by
  cases tuple with
  | nil => exact Nat.zero_le _
  | cons first rest => exact widths first List.mem_cons_self

/-- Literal tuple and class dimensions bound every descriptor before any projection runs. -/
theorem descriptors_sizes (tuple : List Row) (classes : EqualityNormalize.Constraints)
    (count width shape : Nat) (tupleCount : tuple.length ≤ count)
    (widths : ∀ edge ∈ tuple, edge.children.length ≤ width) (classCount : classes.length ≤ shape)
    (pathCounts : ∀ paths ∈ classes, paths.length ≤ shape)
    (depths : ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ shape) :
    (descriptors tuple classes).length ≤ width + shape ∧
      ∀ cell ∈ descriptors tuple classes, Profile count width shape cell := by
  constructor
  · have arity := arity_le tuple width widths
    simp only [descriptors, List.length_append, List.length_map,
      SourceCurrentConjunctionRequirements.columns, MergedPhysicalGroupEdges.columns_length]
    exact Nat.add_le_add arity classCount
  · intro cell member
    change cell ∈ (SourceCurrentConjunctionRequirements.columns tuple).map _ ++ classes.map _ at member
    rcases List.mem_append.mp member with column | pending
    · obtain ⟨nodes, included, rfl⟩ := List.mem_map.mp column
      have small := SourceCurrentConjunctionRequirementNumeric.column_width
        (tuple.map EdgeValue.children) (SourceCurrentConjunctionRequirements.arity tuple) nodes included
      exact Nat.le_trans (by simpa only [List.length_map] using small) tupleCount
    · obtain ⟨paths, included, rfl⟩ := List.mem_map.mp pending
      refine ⟨rfl, ?_, ?_, ?_⟩
      · change (SourceCurrentConjunctionCompletionReads.jobs (tuple.map EdgeValue.children) paths).length ≤ _
        rw [SourceCurrentConjunctionCompletionReads.jobs_length, List.length_map]
        exact Nat.mul_le_mul tupleCount (pathCounts paths included)
      · apply fold_max_le
        intro job member
        obtain ⟨forest, _, selected⟩ := List.mem_flatMap.mp member
        obtain ⟨path, pathIn, rfl⟩ := List.mem_map.mp selected
        exact depths paths included path pathIn
      · apply fold_max_le
        intro job member
        obtain ⟨forest, forestIn, selected⟩ := List.mem_flatMap.mp member
        obtain ⟨path, _, rfl⟩ := List.mem_map.mp selected
        obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp forestIn
        exact widths edge edgeIn

private theorem allocated_profiles (cells : List Cell) (before : Cells) (count width shape : Nat)
    (profiles : ∀ cell ∈ cells, Profile count width shape cell) :
    ∀ handle ∈ (allocateCells cells before).1,
      ∃ cell, SourceCurrentConjunctionRequirementCells.lookup handle (allocateCells cells before).2 = some cell ∧
        Profile count width shape cell := by
  intro handle member
  rw [allocateCells_handles] at member
  obtain ⟨index, inside, same⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at same
  have exactHandle : handle = before.cells.length + index := by omega
  have found : cells[index]? = some cells[index] := List.getElem?_eq_getElem inside
  refine ⟨cells[index], ?_, profiles _ (List.getElem_mem inside)⟩
  change (allocateCells cells before).2.cells[handle]? = some cells[index]
  rw [allocateCells_order, exactHandle, List.getElem?_append_right (Nat.le_add_right _ _)]
  simpa only [Nat.add_sub_cancel_left] using found

private theorem guard_bounds (alphabet : List Guard) (count : Nat) (tuple : List Row)
    (tupleCount : tuple.length ≤ count) (carrier : ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet)
    (classes : EqualityNormalize.Constraints)
    (live : SourceCurrentConjunctionEmptinessRows.combined (tuple.map SourceCurrentConjunctionEquality.edgeView) = some classes) :
    classes.length ≤ shapeThrough alphabet count ∧
      (∀ paths ∈ classes, paths.length ≤ shapeThrough alphabet count) ∧
      ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ shapeThrough alphabet count := by
  have bounded := SourceCurrentConjunctionTupleBounds.combined_bounds alphabet tuple.length
    (tuple.map (fun edge => edge.entry.key.constraint)) (by simp only [List.length_map])
    (by
      intro guard member
      obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
      exact carrier edge included) classes ((SourceCurrentConjunctionTupleBounds.combined_edgeView tuple).trans live)
  have increase := SourceCurrentConjunctionTupleBounds.classShapeBound_le_shapeThrough
    alphabet tuple.length count tupleCount
  exact ⟨Nat.le_trans bounded.1 increase,
    fun paths member => Nat.le_trans (bounded.2.1 paths member) increase,
    fun paths member path selected => Nat.le_trans (bounded.2.2 paths member path selected) increase⟩

/-- The actual fold derives its own class bounds and registers the identical bounded descriptor batch. -/
theorem prepareTuple_sizes (tuple : List Row) (before : Storage) (alphabet : List Guard) (count width : Nat)
    (ready : Ready before.requirements.physical) (resident : Edges before.requirements.physical.heap tuple)
    (tupleCount : tuple.length ≤ count) (widths : ∀ edge ∈ tuple, edge.children.length ≤ width)
    (carrier : ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet) :
    ∃ row after, prepareTuple tuple before = .done row after ∧
      Allocation count width (shapeThrough alphabet count) before row after := by
  obtain ⟨result, done, _, _, foldedClasses, _, _, _⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.requirements.physical.heap
      before.requirements.physical.equality ready.valid ready.fields resident
  let current : Storage := {before with requirements := {before.requirements with
    physical := ⟨before.requirements.physical.heap,
      (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩}}
  cases classified : SourceEqualityInheritedPayload.classes result.payload with
  | none =>
      refine ⟨none, current, ?_, [], ?_, Nat.zero_le _, ?_, ?_, ?_⟩
      · simp only [prepareTuple, done, classified, current]
      · exact (List.append_nil _).symm
      · intro cell member; cases member
      · intro handles impossible; cases impossible
      · intro handles impossible; cases impossible
  | some classes =>
      have bounds := guard_bounds alphabet count tuple tupleCount carrier classes (foldedClasses.symm.trans classified)
      have sizes := descriptors_sizes tuple classes count width (shapeThrough alphabet count)
        tupleCount widths bounds.1 bounds.2.1 bounds.2.2
      let allocated := allocateCells (descriptors tuple classes) current.requirements
      refine ⟨some allocated.1, {current with requirements := allocated.2}, ?_, descriptors tuple classes,
        allocateCells_order _ current.requirements, sizes.1, sizes.2, ?_, ?_⟩
      · simp only [prepareTuple, done, classified, current, allocated]
      · intro handles same
        cases same
        exact allocateCells_handles _ current.requirements
      · intro handles same
        cases same
        exact allocated_profiles _ current.requirements count width _ sizes.2

/-- Current resident payloads and actual records derive all width and guard-carrier premises internally. -/
theorem prepareTuple_current_sizes (tuple : List Row) (before : Storage) (count resource : Nat)
    (ready : Ready before.requirements.physical) (resident : Edges before.requirements.physical.heap tuple)
    (fits : Fits resource before.requirements.physical.heap) (tupleCount : tuple.length ≤ count) :
    ∃ row after, prepareTuple tuple before = .done row after ∧
      Allocation count resource
        (shapeThrough (SourceCurrentConjunctionGuardUniverse.guards before.requirements.physical.heap) count)
        before row after ∧ Fits resource after.requirements.physical.heap := by
  have widths : ∀ edge ∈ tuple, edge.children.length ≤ resource := by
    intro edge member
    have mass := InternedValueMassHeap.resident before.requirements.physical.heap fits.stored edge (resident edge member)
    have length := InternedStoredEncodingWidth.values_length edge.children
    rw [InternedValueMass.edge_children] at mass
    omega
  have known := SourceCurrentConjunctionGuardUniverse.initial before.requirements.physical.heap
    ready.semantic.ready.semantic.1.normal.facts
  have carrier : ∀ edge ∈ tuple, edge.entry.key.constraint ∈
      SourceCurrentConjunctionGuardUniverse.guards before.requirements.physical.heap := by
    intro edge member
    exact known edge.entry.key edge (resident edge member)
  obtain ⟨row, after, actual, sizes⟩ := prepareTuple_sizes tuple before _ count resource
    ready resident tupleCount widths carrier
  have physical := prepareTuple_physical tuple before
  rw [actual] at physical
  have sameHeap := congrArg
    (fun state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula => state.heap) physical
  exact ⟨row, after, actual, sizes, sameHeap.symm ▸ fits⟩

end MicroCFTA.SourceCurrentConjunctionRequirementRowsSizes
