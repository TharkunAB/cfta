import MicroCFTA.SourceCurrentConstrainedCapEditFrame

/-!
# Exact current inventories for shared edit receipts

An edit receipt retains historical slot inventories. A returned query frame
can set its current admission inventory without changing any state or read.
The read verifiers below reuse the existing physical edit effects.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapEditReceipt
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedSharedEditGraph
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedSharedEditEffects (Receipt NodeReceipt ChildrenReceipt RowsReceipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {width : Nat}

/-- Every original ordinary child also satisfies the weaker parent depth bound. -/
theorem node_children {depth : Nat} {entry edges level free}
    (bounded : SourceCurrentConstrainedCap.Cap Plain depth (.node entry edges level free))
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges)
    (child : Value Symbol Guard) (selected : child ∈ edge.children) :
    SourceCurrentConstrainedCap.Cap Plain depth child := by
  have row := SourceCurrentConstrainedCap.node_edge bounded edge member
  cases depth with
  | zero => exact .plain 0 (row.2 child selected)
  | succ depth => exact (row child selected).mono (Nat.le_succ depth)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory next : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap}
variable {before after : SharedState width}

/-- The returned frame replaces current admission while all slot histories stay exact. -/
theorem ready (previous : Ready formulas solver inventory record originals base after)
    (frame : Frame formulas solver next after.checked) :
    Ready formulas solver next record originals base after :=
  ⟨frame.ready, frame.admitted, previous.captured, previous.stored, previous.covered, previous.receipts⟩

/-- A current-inventory change keeps the same physical edit receipt. -/
theorem receipt {memos final}
    (previous : Receipt formulas solver inventory record originals base before after memos final)
    (frame : Frame formulas solver next after.checked) :
    Receipt formulas solver next record originals base before after memos final :=
  ⟨ready previous.ready frame, previous.effects, previous.extension, previous.slots, previous.retained, previous.globals⟩

/-- A node receipt keeps its actual output and selected-domain transport. -/
theorem node_receipt {value result memos final}
    (previous : NodeReceipt formulas solver inventory record originals base value before result after memos final)
    (frame : Frame formulas solver next after.checked) :
    NodeReceipt formulas solver next record originals base value before result after memos final :=
  ⟨receipt previous.toReceipt frame, previous.available, previous.transport⟩

/-- A child receipt keeps every ordered original position at the returned inventory. -/
theorem children_receipt {values results memos final}
    (previous : ChildrenReceipt formulas solver inventory record originals base values before results after memos final)
    (frame : Frame formulas solver next after.checked) :
    ChildrenReceipt formulas solver next record originals base values before results after memos final :=
  ⟨receipt previous.toReceipt frame, previous.available, previous.transport⟩

/-- A row receipt keeps all resident raw edges and ordered child transport. -/
theorem rows_receipt {edges results memos final}
    (previous : RowsReceipt formulas solver inventory record originals base edges before results after memos final)
    (frame : Frame formulas solver next after.checked) :
    RowsReceipt formulas solver next record originals base edges before results after memos final :=
  ⟨receipt previous.toReceipt frame, previous.available, previous.transport⟩

/-- Actual node reads derive their full receipt at the caller's returned frame inventory. -/
theorem node {edits value result memos final}
    {actual : EditNode record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (initial : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (valid : Valid before.checked.native.machine.heap memos)
    (frame : Frame formulas solver next after.checked) :
    NodeReceipt formulas solver next record originals base value before result after memos final := by
  obtain ⟨_chosen, previous⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects reads
    populated nonempty allowed initial available safe valid
  exact node_receipt previous frame

/-- Actual child reads derive their full ordered receipt at the returned frame inventory. -/
theorem children {entries offset values results memos final}
    {actual : EditChildren record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (initial : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : Valid before.checked.native.machine.heap memos)
    (frame : Frame formulas solver next after.checked) :
    ChildrenReceipt formulas solver next record originals base values before results after memos final := by
  obtain ⟨_chosen, previous⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects reads
    populated allowed initial available safe valid
  exact children_receipt previous frame

/-- Actual row reads derive their full raw-row receipt at the returned frame inventory. -/
theorem rows {entries edges results memos final}
    {actual : EditRows record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (initial : Ready formulas solver inventory record originals base before)
    (available : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos)
    (frame : Frame formulas solver next after.checked) :
    RowsReceipt formulas solver next record originals base edges before results after memos final := by
  obtain ⟨_chosen, previous⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads
    populated allowed initial available safe valid
  exact rows_receipt previous frame

/-- The actual row worker retains every original row occurrence. -/
theorem rows_length {entries edges results}
    (actual : EditRows record originals entries edges before results after) : results.length = edges.length := by
  exact EditRows.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ edges _ results _ _ => results.length = edges.length)
    (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; rfl)
    (by intros; simp_all) actual

end MicroCFTA.SourceCurrentConstrainedCapEditReceipt
