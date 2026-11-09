import MicroCFTA.SourceCurrentConjunctionRequirementRowsSizes
import MicroCFTA.SourceCurrentConjunctionRequirementCellsSize
import MicroCFTA.SourceCurrentConjunctionRequirementRowsCompletion
import MicroCFTA.SourceCurrentConjunctionRequirementRowsTrace

/-!
# Current numeric control for actual shared row forcing

Rejected tuples append no cells. A live row appends one bounded descriptor
batch. Cached and missing handles leave both private heaps unchanged.
Actual row forcing retains raw tuple widths on all outcomes. The bounds
use current readiness, resident raw tuples, and a fixed guard carrier.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsNumericControl
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementRowsEffects (RawInputs SpineInputs)
open SourceCurrentConjunctionRequirementCellsSize (size stateSize)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- Every pending tuple has at most the fixed number of original operands. -/
def RawWidths (count : Nat) (before : Storage) : Prop :=
  ∀ spine ∈ before.spines, match spine with
    | .pending tuples => ∀ tuple ∈ tuples, tuple.length ≤ count
    | .done _ => True

/-- Cached row width counts every stored handle occurrence. -/
def spineWidth : Spine Symbol Formula → Nat
  | .done (some (handles, _)) => handles.length
  | .pending _ | .done none => 0

/-- The largest actual cached row supplies a bound without assuming distinct handles. -/
def cachedSize (before : Storage) : Nat :=
  before.spines.foldr (fun spine bound => max (spineWidth spine) bound) 0

/-- A returned live row has bounded handle count; other outcomes emit no row. -/
def ReturnedWidth (bound : Nat) : Outcome Symbol Formula (Option (Handles × Nat)) → Prop
  | .done (some (handles, _)) _ => handles.length ≤ bound
  | .done none _ | .failed _ _ => True

private theorem cached_member (spines : List (Spine Symbol Formula)) (spine : Spine Symbol Formula)
    (member : spine ∈ spines) :
    spineWidth spine ≤ spines.foldr (fun next bound => max (spineWidth next) bound) 0 := by
  induction spines with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

private theorem cached_max_le (spines : List (Spine Symbol Formula)) (bound : Nat)
    (limits : ∀ spine ∈ spines, spineWidth spine ≤ bound) :
    spines.foldr (fun spine previous => max (spineWidth spine) previous) 0 ≤ bound := by
  induction spines with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
      exact Nat.max_le.mpr ⟨limits first List.mem_cons_self,
        ih (fun spine member => limits spine (List.mem_cons_of_mem _ member))⟩

private theorem cached_update (handle : Nat) (replacement : Spine Symbol Formula) (before : Storage) :
    cachedSize (updateSpine handle replacement before) ≤ max (cachedSize before) (spineWidth replacement) := by
  apply cached_max_le
  intro spine member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact Nat.le_trans (cached_member before.spines spine old) (Nat.le_max_left _ _)
  · exact same.symm ▸ Nat.le_max_right _ _

private theorem cached_same {before after : Storage} (same : after.spines = before.spines) :
    cachedSize after = cachedSize before := by
  unfold cachedSize
  rw [same]

/-- Allocating an unforced raw tail leaves every cached row width unchanged. -/
theorem cachedSize_allocate_pending (tuples : List (List Row)) (before : Storage) :
    cachedSize (allocateSpine (.pending tuples) before).2 = cachedSize before := by
  simp only [cachedSize, allocateSpine, List.foldr_append, List.foldr_cons,
    List.foldr_nil, spineWidth, Nat.max_self]

private theorem returned_mono {first last : Nat} (increase : first ≤ last)
    (actual : Outcome Symbol Formula (Option (Handles × Nat)))
    (prior : ReturnedWidth first actual) : ReturnedWidth last actual := by
  cases actual with
  | failed fault after => trivial
  | done row after =>
      cases row with
      | none => trivial
      | some row => exact Nat.le_trans prior increase

private theorem max_mono {firstLeft lastLeft firstRight lastRight : Nat}
    (left : firstLeft ≤ lastLeft) (right : firstRight ≤ lastRight) :
    max firstLeft firstRight ≤ max lastLeft lastRight :=
  Nat.max_le.mpr ⟨Nat.le_trans left (Nat.le_max_left _ _), Nat.le_trans right (Nat.le_max_right _ _)⟩

/-- A fresh batch bounds column widths, path depth, forest width, and job count. -/
noncomputable def freshSize (alphabet : List Guard) (count resource : Nat) : Nat :=
  let shape := shapeThrough alphabet count
  max count (max shape (max resource (count * shape)))

/-- The fresh profile retains each of its four current dimensions. -/
theorem freshSize_ge (alphabet : List Guard) (count resource : Nat) :
    count ≤ freshSize alphabet count resource ∧ shapeThrough alphabet count ≤ freshSize alphabet count resource ∧
      resource ≤ freshSize alphabet count resource ∧ count * shapeThrough alphabet count ≤ freshSize alphabet count resource := by
  exact ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)),
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩

/-- Larger current tuple and resource limits retain every earlier fresh profile. -/
theorem freshSize_mono (alphabet : List Guard) {firstCount lastCount firstResource lastResource : Nat}
    (counts : firstCount ≤ lastCount) (resources : firstResource ≤ lastResource) :
    freshSize alphabet firstCount firstResource ≤ freshSize alphabet lastCount lastResource := by
  have shapes := SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet counts
  exact max_mono counts (max_mono shapes (max_mono resources (Nat.mul_le_mul counts shapes)))

private theorem widths_prepare (count : Nat) (tuple : List Row) (before : Storage) (widths : RawWidths count before) :
    RawWidths count (prepareTuple tuple before).state := by
  intro spine member
  rw [prepareTuple_spines] at member
  exact widths spine member

private theorem widths_update (count handle : Nat) (replacement : Spine Symbol Formula) (before : Storage)
    (widths : RawWidths count before)
    (own : match replacement with | .pending tuples => ∀ tuple ∈ tuples, tuple.length ≤ count | .done _ => True) :
    RawWidths count (updateSpine handle replacement before) := by
  intro spine member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact widths spine old
  · exact same.symm ▸ own

private theorem widths_allocate (count : Nat) (replacement : Spine Symbol Formula) (before : Storage)
    (widths : RawWidths count before)
    (own : match replacement with | .pending tuples => ∀ tuple ∈ tuples, tuple.length ≤ count | .done _ => True) :
    RawWidths count (allocateSpine replacement before).2 := by
  intro spine member
  rcases List.mem_append.mp member with old | fresh
  · exact widths spine old
  · have same : spine = replacement := List.mem_singleton.mp fresh
    exact same.symm ▸ own

private theorem pending_widths (count handle : Nat) (tuples : List (List Row)) (before : Storage)
    (widths : RawWidths count before) (found : lookupSpine handle before = some (.pending tuples)) :
    RawWidths count (nextRow handle before).state := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      exact widths_update count handle (.done none) before widths trivial
  | cons tuple rest ih =>
      have suffix : ∀ next ∈ rest, next.length ≤ count :=
        fun next member => widths (.pending (tuple :: rest)) (List.mem_of_getElem? found)
          next (List.mem_cons_of_mem _ member)
      have retained := widths_prepare count tuple before widths
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          simpa only [prepared, Outcome.state] using retained
      | done row after =>
          have nextWidths : RawWidths count after := by simpa only [prepared, Outcome.state] using retained
          cases row with
          | some handles =>
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact widths_update count handle _ _ (widths_allocate count (.pending rest) after nextWidths suffix) trivial
          | none =>
              have spines := prepareTuple_spines tuple before
              rw [prepared] at spines
              change after.spines = before.spines at spines
              have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
                change after.spines[handle]? = some (.pending (tuple :: rest))
                rw [spines]
                exact found
              rw [nextRow_rejected handle tuple rest before after found prepared]
              exact ih (updateSpine handle (.pending rest) after)
                (widths_update count handle (.pending rest) after nextWidths suffix)
                (lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after afterFound)

/-- Row forcing preserves raw tuple widths on every actual outcome without heap assumptions. -/
theorem nextRow_widths (count handle : Nat) (before : Storage) (widths : RawWidths count before) :
    RawWidths count (nextRow handle before).state := by
  cases found : lookupSpine handle before with
  | none => rw [nextRow_missing handle before found]; exact widths
  | some spine =>
      cases spine with
      | done row => rw [nextRow_hit handle row before found]; exact widths
      | pending tuples => exact pending_widths count handle tuples before widths found

private theorem member_size (cells : List Cell) (cell : Cell) (member : cell ∈ cells) :
    size cell ≤ cells.foldr (fun next bound => max (size next) bound) 0 := by
  induction cells with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

private theorem list_max_le (cells : List Cell) (bound : Nat) (limits : ∀ cell ∈ cells, size cell ≤ bound) :
    cells.foldr (fun cell previous => max (size cell) previous) 0 ≤ bound := by
  induction cells with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
      exact Nat.max_le.mpr ⟨limits first List.mem_cons_self,
        ih (fun cell member => limits cell (List.mem_cons_of_mem _ member))⟩

private theorem profile_size (alphabet : List Guard) (count resource : Nat) (cell : Cell)
    (profile : SourceCurrentConjunctionRequirementRowsSizes.Profile count resource (shapeThrough alphabet count) cell) :
    size cell ≤ freshSize alphabet count resource := by
  have limits := freshSize_ge alphabet count resource
  cases cell with
  | done nodes => cases profile
  | column nodes => exact Nat.le_trans profile limits.1
  | pending cursor =>
      obtain ⟨collected, jobs, depths, widths⟩ := profile
      refine Nat.max_le.mpr ⟨Nat.le_trans depths limits.2.1,
        Nat.max_le.mpr ⟨Nat.le_trans widths limits.2.2.1, ?_⟩⟩
      change cursor.collected.length + cursor.pending.length ≤ _
      rw [collected, List.length_nil, Nat.zero_add]
      exact Nat.le_trans jobs limits.2.2.2

/-- Actual tuple preparation appends at most one current bounded descriptor batch. -/
theorem prepareTuple_bound (tuple : List Row) (before : Storage) (alphabet : List Guard) (count resource : Nat)
    (ready : Ready before.requirements.physical) (resident : Edges before.requirements.physical.heap tuple)
    (tupleCount : tuple.length ≤ count)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.requirements.physical.heap)
    (fits : Fits resource before.requirements.physical.heap) :
    (prepareTuple tuple before).state.requirements.cells.length ≤
        before.requirements.cells.length + resource + shapeThrough alphabet count ∧
      stateSize (prepareTuple tuple before).state.requirements ≤
        max (stateSize before.requirements) (freshSize alphabet count resource) := by
  have widths : ∀ edge ∈ tuple, edge.children.length ≤ resource := by
    intro edge member
    have mass := InternedValueMassHeap.resident before.requirements.physical.heap fits.stored edge (resident edge member)
    have length := InternedStoredEncodingWidth.values_length edge.children
    rw [InternedValueMass.edge_children] at mass
    omega
  obtain ⟨row, after, actual, added, appended, length, profiles, _, _⟩ :=
    SourceCurrentConjunctionRequirementRowsSizes.prepareTuple_sizes tuple before alphabet count resource
      ready resident tupleCount widths (fun edge member => known edge.entry.key edge (resident edge member))
  rw [actual]
  constructor
  · change after.requirements.cells.length ≤ _
    rw [appended, List.length_append]
    omega
  · apply list_max_le
    intro cell member
    change cell ∈ after.requirements.cells at member
    rw [appended] at member
    rcases List.mem_append.mp member with old | fresh
    · exact Nat.le_trans (member_size before.requirements.cells cell old) (Nat.le_max_left _ _)
    · exact Nat.le_trans (profile_size alphabet count resource cell (profiles cell fresh)) (Nat.le_max_right _ _)

private theorem prepared_handles (tuple : List Row) (before after : Storage) (handles : Handles)
    (alphabet : List Guard) (count resource : Nat)
    (ready : Ready before.requirements.physical) (resident : Edges before.requirements.physical.heap tuple)
    (tupleCount : tuple.length ≤ count)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.requirements.physical.heap)
    (fits : Fits resource before.requirements.physical.heap)
    (actual : prepareTuple tuple before = .done (some handles) after) :
    handles.length ≤ resource + shapeThrough alphabet count := by
  have widths : ∀ edge ∈ tuple, edge.children.length ≤ resource := by
    intro edge member
    have mass := InternedValueMassHeap.resident before.requirements.physical.heap fits.stored edge (resident edge member)
    have length := InternedStoredEncodingWidth.values_length edge.children
    rw [InternedValueMass.edge_children] at mass
    omega
  obtain ⟨row, _, prepared, added, _, length, _, range, _⟩ :=
    SourceCurrentConjunctionRequirementRowsSizes.prepareTuple_sizes tuple before alphabet count resource
      ready resident tupleCount widths (fun edge member => known edge.entry.key edge (resident edge member))
  have same := Outcome.done.inj (prepared.symm.trans actual)
  have exactRange := range handles same.1
  rw [exactRange, List.length_range']
  exact length

private theorem pending_bound (handle : Nat) (tuples : List (List Row)) (before : Storage)
    (alphabet : List Guard) (count resource : Nat) (ready : Ready before.requirements.physical)
    (raw : SpineInputs before) (widths : RawWidths count before)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.requirements.physical.heap)
    (fits : Fits resource before.requirements.physical.heap)
    (found : lookupSpine handle before = some (.pending tuples)) :
    (nextRow handle before).state.requirements.cells.length ≤
        before.requirements.cells.length + resource + shapeThrough alphabet count ∧
      stateSize (nextRow handle before).state.requirements ≤
        max (stateSize before.requirements) (freshSize alphabet count resource) ∧
      cachedSize (nextRow handle before).state ≤ max (cachedSize before) (resource + shapeThrough alphabet count) ∧
      ReturnedWidth (max (cachedSize before) (resource + shapeThrough alphabet count)) (nextRow handle before) := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      have cached : cachedSize (updateSpine handle (.done none) before) ≤ cachedSize before := by
        simpa only [spineWidth, Nat.max_zero] using cached_update handle (.done none) before
      exact ⟨by change before.requirements.cells.length ≤ _; omega, Nat.le_max_left _ _,
        Nat.le_trans cached (Nat.le_max_left _ _), trivial⟩
  | cons tuple rest ih =>
      have resident := raw (.pending (tuple :: rest)) (List.mem_of_getElem? found) tuple List.mem_cons_self
      have tupleCount := widths (.pending (tuple :: rest)) (List.mem_of_getElem? found) tuple List.mem_cons_self
      obtain ⟨row, after, prepared, afterReady⟩ :=
        SourceCurrentConjunctionRequirementRowsCompletion.prepareTuple_success tuple before ready resident
      have first := prepareTuple_bound tuple before alphabet count resource ready resident tupleCount known fits
      rw [prepared] at first
      have spines := prepareTuple_spines tuple before
      rw [prepared] at spines
      change after.spines = before.spines at spines
      have cachedSame := cached_same spines
      cases row with
      | some handles =>
          have handleBound := prepared_handles tuple before after handles alphabet count resource ready resident
            tupleCount known fits prepared
          rw [nextRow_live handle tuple rest before after handles found prepared]
          have cached := cached_update handle (.done (some (handles, after.spines.length)))
            (allocateSpine (.pending rest) after).2
          have boundedCache : cachedSize (updateSpine handle (.done (some (handles, after.spines.length)))
                (allocateSpine (.pending rest) after).2) ≤
              max (cachedSize before) (resource + shapeThrough alphabet count) := by
            apply Nat.le_trans cached
            simpa only [cachedSize_allocate_pending, cachedSame, spineWidth] using
              max_mono (Nat.le_refl (cachedSize before)) handleBound
          exact ⟨first.1, first.2, boundedCache, Nat.le_trans handleBound (Nat.le_max_right _ _)⟩
      | none =>
          obtain ⟨_, _, afterEq⟩ := SourceCurrentConjunctionRequirementRowsTrace.prepareTuple_none prepared
          have sameCells := congrArg (fun state : Storage => state.requirements.cells) afterEq
          have physical := prepareTuple_physical tuple before
          rw [prepared] at physical
          have sameHeap : after.requirements.physical.heap = before.requirements.physical.heap := by
            simpa only [Outcome.state] using congrArg
              (fun state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula => state.heap) physical
          have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [spines]
            exact found
          have afterRaw : SpineInputs after := by
            intro spine member
            rw [spines] at member
            change RawInputs after.requirements.physical.heap spine
            rw [sameHeap]
            exact raw spine member
          have suffixRaw : RawInputs after.requirements.physical.heap (.pending rest) :=
            fun next member => afterRaw (.pending (tuple :: rest)) (List.mem_of_getElem? afterFound)
              next (List.mem_cons_of_mem _ member)
          have nextRaw : SpineInputs (updateSpine handle (.pending rest) after) := by
            intro spine member
            rcases List.mem_or_eq_of_mem_set member with old | same
            · exact afterRaw spine old
            · exact same.symm ▸ suffixRaw
          have afterWidths : RawWidths count after := by
            simpa only [prepared, Outcome.state] using widths_prepare count tuple before widths
          have suffixWidths : ∀ next ∈ rest, next.length ≤ count :=
            fun next member => afterWidths (.pending (tuple :: rest)) (List.mem_of_getElem? afterFound)
              next (List.mem_cons_of_mem _ member)
          have nextWidths := widths_update count handle (.pending rest) after afterWidths suffixWidths
          have nextFound := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after afterFound
          have later := ih (updateSpine handle (.pending rest) after) afterReady nextRaw nextWidths
            (sameHeap.symm ▸ known) (sameHeap.symm ▸ fits) nextFound
          have cachedNext : cachedSize (updateSpine handle (.pending rest) after) ≤ cachedSize before := by
            simpa only [spineWidth, Nat.max_zero, cachedSame] using cached_update handle (.pending rest) after
          rw [nextRow_rejected handle tuple rest before after found prepared]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa only [updateSpine, sameCells] using later.1
          · simpa only [updateSpine, stateSize, sameCells] using later.2.1
          · exact Nat.le_trans later.2.2.1 (max_mono cachedNext (Nat.le_refl _))
          · exact returned_mono (max_mono cachedNext (Nat.le_refl _)) _ later.2.2.2

/-- Every actual row force adds at most one bounded batch and retains all raw tuple widths. -/
theorem nextRow_bound (handle : Nat) (before : Storage) (alphabet : List Guard) (count resource : Nat)
    (ready : Ready before.requirements.physical) (raw : SpineInputs before) (widths : RawWidths count before)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.requirements.physical.heap)
    (fits : Fits resource before.requirements.physical.heap) :
    (nextRow handle before).state.requirements.cells.length ≤
        before.requirements.cells.length + resource + shapeThrough alphabet count ∧
      stateSize (nextRow handle before).state.requirements ≤
        max (stateSize before.requirements) (freshSize alphabet count resource) ∧
      RawWidths count (nextRow handle before).state ∧
      cachedSize (nextRow handle before).state ≤ max (cachedSize before) (resource + shapeThrough alphabet count) ∧
      ReturnedWidth (max (cachedSize before) (resource + shapeThrough alphabet count)) (nextRow handle before) := by
  have bounded : (nextRow handle before).state.requirements.cells.length ≤
        before.requirements.cells.length + resource + shapeThrough alphabet count ∧
      stateSize (nextRow handle before).state.requirements ≤
        max (stateSize before.requirements) (freshSize alphabet count resource) ∧
      cachedSize (nextRow handle before).state ≤ max (cachedSize before) (resource + shapeThrough alphabet count) ∧
      ReturnedWidth (max (cachedSize before) (resource + shapeThrough alphabet count)) (nextRow handle before) := by
    cases found : lookupSpine handle before with
    | none =>
        rw [nextRow_missing handle before found]
        exact ⟨by change before.requirements.cells.length ≤ _; omega, Nat.le_max_left _ _, Nat.le_max_left _ _, trivial⟩
    | some spine =>
        cases spine with
        | done row =>
            rw [nextRow_hit handle row before found]
            refine ⟨by change before.requirements.cells.length ≤ _; omega, Nat.le_max_left _ _, Nat.le_max_left _ _, ?_⟩
            cases row with
            | none => trivial
            | some row =>
                exact Nat.le_trans (cached_member before.spines (.done (some row)) (List.mem_of_getElem? found))
                  (Nat.le_max_left _ _)
        | pending tuples => exact pending_bound handle tuples before alphabet count resource ready raw widths known fits found
  exact ⟨bounded.1, bounded.2.1, nextRow_widths count handle before widths, bounded.2.2⟩

end MicroCFTA.SourceCurrentConjunctionRequirementRowsNumericControl
