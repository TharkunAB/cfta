import MicroCFTA.SourceCurrentConjunctionRequirementCells

/-!
# Shared requirement rows from actual tuple equality

Tuple preparation runs the existing allocated equality fold first.
Contradiction creates no requirement cells. A live tuple allocates column
cells before its class cursors. Allocation does not force those cells or
change the native physical state returned by the equality fold.

A row-spine handle caches one live row and its unforced tail. Forcing skips
contradictory tuples in source order. It retains each actual failed state.
A cached row returns without another fold or projection. These private
heaps are not yet selected by the conjunction worklist.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRows
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- Each row stores handles in the literal requirement order. -/
abbrev Handles := List Nat

/-- A spine retains raw tuples or the cached first row and its tail handle. -/
inductive Spine (Symbol Formula : Type) where
  | pending (tuples : List (List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))))
  | done (row : Option (Handles × Nat))

/-- Projection cells and row-spine cells retain their separate stable handles. -/
structure State (Symbol Formula : Type) where
  requirements : SourceCurrentConjunctionRequirementCells.State Symbol Formula
  spines : List (Spine Symbol Formula)

/-- Equality faults and missing row-spine handles retain distinct diagnostics. -/
inductive Fault where
  | rows (actual : SourceCurrentConjunctionRowsWorker.Fault)
  | missing (handle : Nat)

/-- Every result retains both private heaps and the actual native physical state. -/
inductive Outcome (Symbol Formula Output : Type) where
  | done (output : Output) (state : State Symbol Formula)
  | failed (fault : Fault) (state : State Symbol Formula)

/-- Successful and failed row preparation expose the same reached state. -/
def Outcome.state : Outcome Symbol Formula Output → State Symbol Formula
  | .done _ state | .failed _ state => state

/-- Initialize private row storage without changing the supplied physical state. -/
def initial (before : Physical Symbol Formula) : State Symbol Formula :=
  ⟨SourceCurrentConjunctionRequirementCells.initial before, []⟩

/-- Allocate the literal cell list in order through the existing cell allocator. -/
def allocateCells : List Cell → Cells → Handles × Cells
  | [], before => ([], before)
  | cell :: rest, before =>
      let first := SourceCurrentConjunctionRequirementCells.allocate cell before
      let tail := allocateCells rest first.2
      (first.1 :: tail.1, tail.2)

/-- Cell allocation retains the identical complete native physical state. -/
theorem allocateCells_physical (cells : List Cell) (before : Cells) :
    (allocateCells cells before).2.physical = before.physical := by
  induction cells generalizing before with
  | nil => rfl
  | cons cell rest ih =>
      change (allocateCells rest (SourceCurrentConjunctionRequirementCells.allocate cell before).2).2.physical = _
      exact ih _

/-- The allocated descriptors occupy the exact ordered suffix of the cell heap. -/
theorem allocateCells_order (cells : List Cell) (before : Cells) :
    (allocateCells cells before).2.cells = before.cells ++ cells := by
  induction cells generalizing before with
  | nil => simp only [allocateCells, List.append_nil]
  | cons cell rest ih =>
      change (allocateCells rest (SourceCurrentConjunctionRequirementCells.allocate cell before).2).2.cells = _
      rw [ih]
      simp only [SourceCurrentConjunctionRequirementCells.allocate, List.append_assoc,
        List.cons_append, List.nil_append]

/-- Ordered handles retain every original descriptor position without deduplication. -/
theorem allocateCells_handles (cells : List Cell) (before : Cells) :
    (allocateCells cells before).1 = List.range' before.cells.length cells.length := by
  induction cells generalizing before with
  | nil => rfl
  | cons cell rest ih =>
      change before.cells.length :: (allocateCells rest
        (SourceCurrentConjunctionRequirementCells.allocate cell before).2).1 =
        List.range' before.cells.length (rest.length + 1)
      rw [ih]
      simp only [List.range'_succ, SourceCurrentConjunctionRequirementCells.allocate,
        List.length_append, List.length_singleton]

/-- Child columns precede class cursors with the literal forest-major path jobs. -/
def descriptors (tuple : List Row) (constraints : EqualityNormalize.Constraints) : List Cell :=
  (SourceCurrentConjunctionRequirements.columns tuple).map (fun nodes => .column nodes) ++
    constraints.map (fun paths => .pending
      (SourceCurrentConjunctionRequirementPull.start (tuple.map EdgeValue.children) paths))

/-- Fold the actual tuple equalities, then allocate only its live requirement cells. -/
noncomputable def prepareTuple (tuple : List Row) (before : State Symbol Formula) :
    Outcome Symbol Formula (Option Handles) :=
  let folded := SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality
  let current := {before with requirements := {before.requirements with
    physical := ⟨before.requirements.physical.heap, folded.2⟩}}
  match folded.1 with
  | .error message => .failed (.rows (.equality message)) current
  | .ok none => .failed (.rows .missingEquality) current
  | .ok (some result) =>
      match SourceEqualityInheritedPayload.classes result.payload with
      | none => .done none current
      | some constraints =>
          let allocated := allocateCells (descriptors tuple constraints) current.requirements
          .done (some allocated.1) {current with requirements := allocated.2}

/-- Every preparation outcome retains exactly the native state after its equality fold. -/
theorem prepareTuple_physical (tuple : List Row) (before : State Symbol Formula) :
    (prepareTuple tuple before).state.requirements.physical =
      ⟨before.requirements.physical.heap,
        (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩ := by
  unfold prepareTuple
  dsimp only
  split
  · rfl
  · rfl
  · split
    · rfl
    · exact allocateCells_physical _ _

/-- Preparation never changes any existing row-spine cell. -/
theorem prepareTuple_spines (tuple : List Row) (before : State Symbol Formula) :
    (prepareTuple tuple before).state.spines = before.spines := by
  unfold prepareTuple
  dsimp only
  split
  · rfl
  · rfl
  · split <;> rfl

/-- Contradiction rejects the tuple without allocating or forcing a requirement cell. -/
theorem prepareTuple_contradiction (tuple : List Row) (before : State Symbol Formula)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (folded : SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality =
      (.ok (some .contradiction), operations)) :
    prepareTuple tuple before = .done none
      {before with requirements := {before.requirements with
        physical := ⟨before.requirements.physical.heap, operations⟩}} := by
  simp only [prepareTuple, folded, SourceEqualityConstraintAllocation.Value.payload,
    SourceEqualityInheritedPayload.classes, Option.map_none]

/-- Live preparation returns the ordered handles at the same actual fold state. -/
theorem prepareTuple_live (tuple : List Row) (before : State Symbol Formula)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (result : SourceEqualityConstraintAllocation.Value) (constraints : EqualityNormalize.Constraints)
    (folded : SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality =
      (.ok (some result), operations))
    (classes : SourceEqualityInheritedPayload.classes result.payload = some constraints) :
    let current : Cells := {before.requirements with
      physical := ⟨before.requirements.physical.heap, operations⟩}
    let allocated := allocateCells (descriptors tuple constraints) current
    prepareTuple tuple before = .done (some allocated.1) {before with requirements := allocated.2} := by
  simp only [prepareTuple, folded, classes]

/-- Read a row-spine cell without forcing equality or requirement work. -/
def lookupSpine (handle : Nat) (before : State Symbol Formula) : Option (Spine Symbol Formula) :=
  before.spines[handle]?

/-- Append one row-spine cell and return its stable handle. -/
def allocateSpine (cell : Spine Symbol Formula) (before : State Symbol Formula) : Nat × State Symbol Formula :=
  (before.spines.length, {before with spines := before.spines ++ [cell]})

/-- Update one existing row-spine handle without inserting another cell. -/
def updateSpine (handle : Nat) (cell : Spine Symbol Formula) (before : State Symbol Formula) : State Symbol Formula :=
  {before with spines := before.spines.set handle cell}

/-- The allocated tail handle reads the exact unforced row suffix. -/
theorem lookupSpine_allocate (cell : Spine Symbol Formula) (before : State Symbol Formula) :
    lookupSpine (allocateSpine cell before).1 (allocateSpine cell before).2 = some cell := by
  simp [lookupSpine, allocateSpine]

/-- Publishing a row retains its original handle. -/
theorem lookupSpine_update (handle : Nat) (original replacement : Spine Symbol Formula)
    (before : State Symbol Formula) (found : lookupSpine handle before = some original) :
    lookupSpine handle (updateSpine handle replacement before) = some replacement := by
  cases before with
  | mk requirements spines =>
      change spines[handle]? = some original at found
      change (spines.set handle replacement)[handle]? = some replacement
      induction spines generalizing handle with
      | nil => cases handle <;> cases found
      | cons first rest ih =>
          cases handle with
          | zero => rfl
          | succ handle => exact ih handle found

private noncomputable def pullRows (handle : Nat) : List (List Row) → State Symbol Formula →
    Outcome Symbol Formula (Option (Handles × Nat))
  | [], before => .done none (updateSpine handle (.done none) before)
  | tuple :: rest, before =>
      match prepareTuple tuple before with
      | .failed fault after => .failed fault after
      | .done none after => pullRows handle rest (updateSpine handle (.pending rest) after)
      | .done (some row) after =>
          let tail := allocateSpine (.pending rest) after
          let result := some (row, tail.1)
          .done result (updateSpine handle (.done result) tail.2)

/-- Force one stable row-spine head and skip only actual contradictory tuples. -/
noncomputable def nextRow (handle : Nat) (before : State Symbol Formula) :
    Outcome Symbol Formula (Option (Handles × Nat)) :=
  match lookupSpine handle before with
  | none => .failed (.missing handle) before
  | some (.done row) => .done row before
  | some (.pending tuples) => pullRows handle tuples before

/-- A cached row head returns at the identical complete state without another fold. -/
theorem nextRow_hit (handle : Nat) (row : Option (Handles × Nat)) (before : State Symbol Formula)
    (found : lookupSpine handle before = some (.done row)) :
    nextRow handle before = .done row before := by
  simp only [nextRow, found]

/-- A missing row-spine handle fails before any physical operation. -/
theorem nextRow_missing (handle : Nat) (before : State Symbol Formula)
    (absent : lookupSpine handle before = none) :
    nextRow handle before = .failed (.missing handle) before := by
  simp only [nextRow, absent]

/-- An exhausted raw suffix publishes the end at the same row-spine handle. -/
theorem nextRow_nil (handle : Nat) (before : State Symbol Formula)
    (found : lookupSpine handle before = some (.pending [])) :
    nextRow handle before = .done none (updateSpine handle (.done none) before) := by
  simp only [nextRow, found, pullRows]

/-- A failed tuple preparation retains its exact fault and reached state. -/
theorem nextRow_failed (handle : Nat) (tuple : List Row) (rest : List (List Row))
    (before after : State Symbol Formula) (fault : Fault)
    (found : lookupSpine handle before = some (.pending (tuple :: rest)))
    (prepared : prepareTuple tuple before = .failed fault after) :
    nextRow handle before = .failed fault after := by
  simp only [nextRow, found, pullRows, prepared]

/-- Rejection retains its actual fold state before entering the next raw tuple. -/
theorem nextRow_rejected (handle : Nat) (tuple : List Row) (rest : List (List Row))
    (before after : State Symbol Formula)
    (found : lookupSpine handle before = some (.pending (tuple :: rest)))
    (prepared : prepareTuple tuple before = .done none after) :
    nextRow handle before = nextRow handle (updateSpine handle (.pending rest) after) := by
  have retained := prepareTuple_spines tuple before
  rw [prepared] at retained
  change after.spines = before.spines at retained
  have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
    change after.spines[handle]? = some (.pending (tuple :: rest))
    rw [retained]
    exact found
  have continued := lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after afterFound
  simp only [nextRow, found, pullRows, prepared, continued]

/-- A live row caches the same handles and an unforced tail at the original head handle. -/
theorem nextRow_live (handle : Nat) (tuple : List Row) (rest : List (List Row))
    (before after : State Symbol Formula) (row : Handles)
    (found : lookupSpine handle before = some (.pending (tuple :: rest)))
    (prepared : prepareTuple tuple before = .done (some row) after) :
    let tail := allocateSpine (.pending rest) after
    let result := some (row, tail.1)
    nextRow handle before = .done result (updateSpine handle (.done result) tail.2) := by
  simp only [nextRow, found, pullRows, prepared]

/-- The cached live head retains the exact shorter raw suffix at its fresh tail handle. -/
theorem nextRow_live_tail (handle : Nat) (tuple : List Row) (rest : List (List Row))
    (before after : State Symbol Formula) (row : Handles)
    (found : lookupSpine handle before = some (.pending (tuple :: rest)))
    (prepared : prepareTuple tuple before = .done (some row) after) :
    let tail := allocateSpine (.pending rest) after
    let result := some (row, tail.1)
    lookupSpine tail.1 (updateSpine handle (.done result) tail.2) = some (.pending rest) ∧
      rest.length < (tuple :: rest).length := by
  have retained := prepareTuple_spines tuple before
  rw [prepared] at retained
  change after.spines = before.spines at retained
  have inside : handle < after.spines.length := by
    have original : handle < before.spines.length := (List.getElem?_eq_some_iff.mp found).1
    simpa only [retained] using original
  constructor
  · change ((after.spines ++ [Spine.pending rest]).set handle
      (Spine.done (some (row, after.spines.length))))[after.spines.length]? = some (Spine.pending rest)
    rw [List.getElem?_set_ne (by omega)]
    simp
  · exact Nat.lt_succ_self _

end MicroCFTA.SourceCurrentConjunctionRequirementRows
