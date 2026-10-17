import MicroCFTA.SourceCurrentConstrainedCapEditForecast
import MicroCFTA.SourceCurrentConstrainedCapEditReceipt
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability

/-!
# Initial resource schedules for ordered shared edit scans

The smaller-trie producer supplies each selected child. Original list
lengths determine the scan schedule before execution. Each returned Frame,
inventory, target table, Merge memo, and global bundle enters the suffix.
The node producer is an induction hypothesis, not a completed future call.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapEditScans
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects (NodeReceipt ChildrenReceipt RowsReceipt)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
namespace Forecast
export SourceCurrentConstrainedCapEditForecast
  (scalar scalar_mono stageProfile stageFuel stage_ge stageFuel_mono stage_constructor_profile
    planProfile plan_ge plan_mono scan scan_ge scan_child scan_mono scan_count_mono rowStep rowStep_ge rowStep_mono)
end Forecast
namespace Worker
export SourceCurrentAllocatedSharedEditWorker (edit children rows work Outcome)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Finite syntax reserves one ordinary and one recursive phase per level. -/
def editFuel (level : Nat) : Nat := 2 * level + 2

/-- The induction hypothesis constructs each smaller node from its initial facts. -/
def NodeComplete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (base : Heap) (inputDepth level : Nat) : Prop :=
  ∀ (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile : Profile),
    sizeOf edits ≤ level → Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Frame formulas solver inventory before.checked →
    Fits profile before.checked → Available before.checked.native.machine.heap input → Safe edits input →
    Cap inputDepth input → Stored record originals before →
    ∀ (memos : Memos), Valid before.checked.native.machine.heap memos →
    Room bits (Forecast.planProfile record originals.length level profile) →
    ∃ result after next final, ∃ actual : EditNode record originals edits input before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base input before result after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.planProfile record originals.length level profile) after.checked ∧
      Stored record originals after ∧
      Worker.edit record originals (editFuel level)
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile))
        edits input before = .done result after

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (inputDepth level : Nat)

/-- An ordered child scan derives every reached reservation from one initial ceiling. -/
theorem children
    (node : NodeComplete (bits := bits) formulas solver record originals base inputDepth level)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (offset : Nat) (values : List (Value Symbol Guard)) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile ceiling : Profile)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (caps : ∀ value ∈ values, Cap inputDepth value) (stored : Stored record originals before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (bounded : Le (Forecast.scan (Forecast.planProfile record originals.length level) values.length profile) ceiling)
    (room : Room bits ceiling) :
    ∃ results after next final, ∃ actual : EditChildren record originals entries offset values before results after,
      ChildrenReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.scan (Forecast.planProfile record originals.length level) values.length profile) after.checked ∧
      Stored record originals after ∧
      Worker.children (Worker.edit record originals (editFuel level)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)) entries offset values before = .done results after := by
  induction values generalizing offset before inventory profile memos with
  | nil =>
      have reads : ChildrenReads formulas solver base (EditChildren.nil (record := record) (originals := originals)
          (entries := entries) (index := offset) (state := before)) memos memos := .nil
      exact ⟨[], before, inventory, memos, .nil, reads,
        SourceCurrentConstrainedCapEditReceipt.children reads populated allowed ready available safe valid frame,
        frame, fits, stored, rfl⟩
  | cons value values ih =>
      let nextProfile := Forecast.planProfile record originals.length level profile
      have later : Le nextProfile ceiling :=
        (Forecast.scan_child (Forecast.planProfile record originals.length level)
          (Forecast.plan_ge record originals.length level) (by simp only [List.length_cons]; omega) profile).trans bounded
      have tailAvailable : Values before.checked.native.machine.heap values :=
        fun original member => available original (List.mem_cons_of_mem _ member)
      have tailCaps : ∀ original ∈ values, Cap inputDepth original :=
        fun original member => caps original (List.mem_cons_of_mem _ member)
      cases found : SourceEqualityNeededMap.lookup (offset : Int) entries with
      | none =>
          obtain ⟨results, after, next, final, rest, restReads, _receipt, returned, finalFits, finalStored, done⟩ :=
            ih (offset + 1) before inventory nextProfile ready frame
              (fits.mono (Forecast.plan_ge record originals.length level profile)) tailAvailable
              (children_tail safe) tailCaps stored memos valid bounded
          have reads : ChildrenReads formulas solver base (.unselected (value := value) offset found rest) memos final :=
            .unselected (value := value) (absent := found) (rest := rest) restReads
          refine ⟨value :: results, after, next, final, .unselected offset found rest, reads,
            SourceCurrentConstrainedCapEditReceipt.children reads populated allowed ready available safe valid returned,
            returned, finalFits, finalStored, ?_⟩
          simp only [Worker.children, found, done, SourceCurrentAllocatedSharedEditWorker.Outcome.bind]
      | some edits =>
          have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
          have supported := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
            by simpa only [Populated] using populated) _ _ member
          have selected : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
          have firstSafe := safe 0 _ (by simpa using found) value rfl
          obtain ⟨result, middle, currentInventory, current, first, firstReads, firstReceipt,
              firstFrame, firstFits, firstStored, firstDone⟩ :=
            node edits value before inventory profile (sizes _ _ member) supported.1 supported.2 selected
              ready frame fits (available _ List.mem_cons_self) firstSafe (caps _ List.mem_cons_self)
              stored memos valid (room.mono later)
          have enough := Forecast.stageFuel_mono record originals.length later
          have lifted := SourceCurrentAllocatedSharedEditWorkerStability.edit_done_stable firstDone
            (Nat.le_refl _) enough enough enough enough enough
          obtain ⟨results, after, next, final, rest, restReads, _receipt, returned, finalFits, finalStored, done⟩ :=
            ih (offset + 1) middle currentInventory nextProfile firstReceipt.ready firstFrame firstFits
              (fun original present => firstReceipt.effects.keeps.available original (tailAvailable original present))
              (children_tail safe) tailCaps firstStored current firstReceipt.globals.valid bounded
          have reads : ChildrenReads formulas solver base (.selected offset found first rest) memos final :=
            .selected firstReads restReads
          refine ⟨result :: results, after, next, final, .selected offset found first rest, reads,
            SourceCurrentConstrainedCapEditReceipt.children reads populated allowed ready available safe valid returned,
            returned, finalFits, finalStored, ?_⟩
          simp only [Worker.children, found, lifted, SourceCurrentAllocatedSharedEditWorker.Outcome.bind, done]

/-- Ordered raw rows use their original child limits and retain each exact constructor return. -/
theorem rows
    (node : NodeComplete (bits := bits) formulas solver record originals base inputDepth level)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (limit : Nat) (edges : List (EdgeValue Symbol Guard)) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile ceiling : Profile)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (resident : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (caps : ∀ edge ∈ edges, ∀ child ∈ edge.children, Cap inputDepth child)
    (widths : ∀ edge ∈ edges, edge.children.length ≤ limit) (limitFits : limit ≤ Forecast.scalar profile)
    (stored : Stored record originals before) (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (bounded : Le (Forecast.scan (Forecast.rowStep record originals.length level limit) edges.length profile) ceiling)
    (room : Room bits ceiling) :
    ∃ results after next final, ∃ actual : EditRows record originals entries edges before results after,
      RowsReads formulas solver base actual memos final ∧
      RowsReceipt formulas solver next record originals base edges before results after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.scan (Forecast.rowStep record originals.length level limit) edges.length profile) after.checked ∧
      Stored record originals after ∧
      Worker.rows (Worker.edit record originals (editFuel level)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)) entries edges before = .done results after := by
  induction edges generalizing before inventory profile memos with
  | nil =>
      have reads : RowsReads formulas solver base (EditRows.nil (record := record) (originals := originals)
          (entries := entries) (state := before)) memos memos := .nil
      exact ⟨[], before, inventory, memos, .nil, reads,
        SourceCurrentConstrainedCapEditReceipt.rows reads populated allowed ready resident safe valid frame,
        frame, fits, stored, rfl⟩
  | cons edge edges ih =>
      let childrenProfile := Forecast.scan (Forecast.planProfile record originals.length level) limit profile
      let nextProfile := Forecast.rowStep record originals.length level limit profile
      have afterRow : Le nextProfile ceiling :=
        (Forecast.scan_child (Forecast.rowStep record originals.length level limit)
          (Forecast.rowStep_ge record originals.length level limit)
          (by simp only [List.length_cons]; omega) profile).trans bounded
      have childBounds : Le (Forecast.scan (Forecast.planProfile record originals.length level) edge.children.length profile)
          ceiling :=
        (Forecast.scan_count_mono _ (Forecast.plan_ge record originals.length level)
          (widths edge List.mem_cons_self) profile).trans
          ((Forecast.stage_ge record originals.length childrenProfile).trans afterRow)
      have original := resident edge List.mem_cons_self
      have available := ready.checked.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge original
      obtain ⟨values, middle, childInventory, current, childrenActual, childReads, childReceipt,
          childFrame, childFits, childStored, childDone⟩ :=
        children formulas solver record originals base inputDepth level node entries sizes 0 edge.children before
          inventory profile ceiling populated allowed ready frame fits available (safe edge List.mem_cons_self)
          (caps edge List.mem_cons_self) stored memos valid childBounds room
      have paddedFits : Fits childrenProfile middle.checked := childFits.mono
        (Forecast.scan_count_mono _ (Forecast.plan_ge record originals.length level)
          (widths edge List.mem_cons_self) profile)
      have valueLength : values.length ≤ limit := by
        rw [children_length childrenActual]
        exact widths edge List.mem_cons_self
      have field := (ready.checked.good.fields edge.entry.key edge original).grows childReceipt.effects.grows
      have built := SourceCurrentConstrainedCapEditFrame.edge childrenProfile limit childFrame paddedFits childReceipt.ready
        edge.entry.key.symbol edge.entry.key.constraint values field childReceipt.available valueLength childStored
      let result := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap
      have edgeFrame : Frame formulas solver childInventory (advanceHeap middle result.2).checked := built.1
      have edgeStored : Stored record originals (advanceHeap middle result.2) := built.2.2.1
      have edgeReady : Ready formulas solver childInventory record originals base (advanceHeap middle result.2) := built.2.2.2.1
      have edgeEffects := built.2.2.2.2.1
      have limitAfter : limit ≤ Forecast.scalar childrenProfile := Nat.le_trans limitFits
        (Forecast.scalar_mono (Forecast.scan_ge _ (Forecast.plan_ge record originals.length level) limit profile))
      have edgeFits : Fits nextProfile (advanceHeap middle result.2).checked :=
        built.2.1.mono (Forecast.stage_constructor_profile record originals.length childrenProfile limitAfter)
      have kept := childReceipt.effects.keeps.trans edgeEffects.keeps
      have edgeValid := SourceQueryUnfoldMemo.valid_grows middle.checked.native.machine.heap result.2
        childReceipt.ready.checked.semantic edgeEffects.keeps current childReceipt.globals.valid
      have nextLimit : limit ≤ Forecast.scalar nextProfile := Nat.le_trans limitFits
        (Forecast.scalar_mono (Forecast.rowStep_ge record originals.length level limit profile))
      obtain ⟨results, after, next, final, rest, restReads, _receipt, returned, finalFits, finalStored, done⟩ :=
        ih (advanceHeap middle result.2) childInventory nextProfile edgeReady edgeFrame edgeFits
          (fun original member => InternedEdgeResidency.edge_grows _ _ kept.growth original
            (resident original (List.mem_cons_of_mem _ member)))
          (fun original member => safe original (List.mem_cons_of_mem _ member))
          (fun original member => caps original (List.mem_cons_of_mem _ member))
          (fun original member => widths original (List.mem_cons_of_mem _ member)) nextLimit edgeStored current edgeValid bounded
      have made : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
          middle.checked.native.machine.heap = (result.1, result.2) := rfl
      let actual : EditRows record originals entries (edge :: edges) before (result.1 :: results) after :=
        .cons childrenActual made rest
      have reads : RowsReads formulas solver base actual memos final :=
        .cons (children := childrenActual) (rebuilt := made) (rest := rest) childReads restReads
      refine ⟨result.1 :: results, after, next, final, actual, reads,
        SourceCurrentConstrainedCapEditReceipt.rows reads populated allowed ready resident safe valid returned,
        returned, finalFits, finalStored, ?_⟩
      simp only [Worker.rows, childDone, SourceCurrentAllocatedSharedEditWorker.Outcome.bind, Worker.work, done]

end MicroCFTA.SourceCurrentConstrainedCapEditScans
