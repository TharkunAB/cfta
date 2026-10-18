import MicroCFTA.SourceCurrentEditGuardBudget
import MicroCFTA.SourceCurrentEditFrame
import MicroCFTA.SourceCurrentConstrainedCapEditForecast
import MicroCFTA.SourceCurrentConstrainedCapEditReceipt
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability

/-!
# Initial finite guard schedules for shared edit scans

A fixed global ceiling bounds each smaller-trie producer. Original list
lengths bound the number of carrier extensions before execution. Each
actual Frame, inventory, slot table, Merge memo, and carrier enters the
suffix. NodeComplete is the strict syntax induction hypothesis.
-/
namespace MicroCFTA.SourceCurrentEditGuardScans
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects (NodeReceipt ChildrenReceipt RowsReceipt)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
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
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "advanceAlphabet" => SourceCurrentNativeGuardAlphabet.advance
local notation "nodeBound" => SourceCurrentEditGuardBudget.nodeBound
private theorem advance_scan (alphabet : List Guard) (length steps : Nat) :
    advanceAlphabet (advanceAlphabet alphabet steps) (length * steps) =
      advanceAlphabet alphabet ((length + 1) * steps) := by
  rw [← SourceCurrentNativeGuardAlphabet.advance_add, Nat.add_mul, Nat.one_mul]
  congr 1
  omega

variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Finite syntax reserves one ordinary and one recursive phase per level. -/
def editFuel (level : Nat) : Nat := 2 * level + 2

/-- The induction hypothesis constructs each smaller node from its initial facts. -/
def NodeComplete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (base : Heap) (level : Nat) (ceiling : Profile) : Prop :=
  ∀ (alphabet : List Guard) (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile : Profile),
    sizeOf edits ≤ level → Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Frame formulas solver inventory before.checked →
    Fits profile before.checked → Available before.checked.native.machine.heap input → Safe edits input →
    ∀ (memos : Memos), Valid before.checked.native.machine.heap memos →
    Le (Forecast.planProfile record originals.length level profile) ceiling → Room bits ceiling →
    Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap →
    ∃ result after next final, ∃ actual : EditNode record originals edits input before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base input before result after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.planProfile record originals.length level profile) after.checked ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet (nodeBound record originals.length ceiling level))
        after.checked.native.machine.heap ∧
      Worker.edit record originals (editFuel level)
        (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)
        edits input before = .done result after

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (level : Nat)

/-- An ordered child scan derives every reached reservation from one initial ceiling. -/
theorem children
    (alphabet : List Guard) (ceiling : Profile)
    (node : NodeComplete (bits := bits) formulas solver record originals base level ceiling)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (offset : Nat) (values : List (Value Symbol Guard)) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile : Profile)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (bounded : Le (Forecast.scan (Forecast.planProfile record originals.length level) values.length profile) ceiling)
    (room : Room bits ceiling)
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ results after next final, ∃ actual : EditChildren record originals entries offset values before results after,
      ChildrenReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.scan (Forecast.planProfile record originals.length level) values.length profile) after.checked ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet
        (values.length * nodeBound record originals.length ceiling level)) after.checked.native.machine.heap ∧
      Worker.children (Worker.edit record originals (editFuel level)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)) entries offset values before = .done results after := by
  induction values generalizing alphabet offset before inventory profile memos with
  | nil =>
      have reads : ChildrenReads formulas solver base (EditChildren.nil (record := record) (originals := originals)
          (entries := entries) (index := offset) (state := before)) memos memos := .nil
      exact ⟨[], before, inventory, memos, .nil, reads,
        SourceCurrentConstrainedCapEditReceipt.children reads populated allowed ready available safe valid frame,
        frame, fits, by simpa only [List.length_nil, Nat.zero_mul,
          SourceCurrentNativeGuardAlphabet.advance_zero] using knownAlphabet, rfl⟩
  | cons value values ih =>
      let steps := nodeBound record originals.length ceiling level
      let nextProfile := Forecast.planProfile record originals.length level profile
      have later : Le nextProfile ceiling :=
        (Forecast.scan_child (Forecast.planProfile record originals.length level)
          (Forecast.plan_ge record originals.length level) (by simp only [List.length_cons]; omega) profile).trans bounded
      have tailAvailable : Values before.checked.native.machine.heap values :=
        fun original member => available original (List.mem_cons_of_mem _ member)
      cases found : SourceEqualityNeededMap.lookup (offset : Int) entries with
      | none =>
          have paddedKnown : Carrier (fun guard => guard ∈ advanceAlphabet alphabet steps)
              before.checked.native.machine.heap := fun key edge found =>
            SourceCurrentNativeGuardAlphabet.mem_advance_of_mem (knownAlphabet key edge found) steps
          obtain ⟨results, after, next, final, rest, restReads, _receipt, returned, finalFits, restKnown, done⟩ :=
            ih (advanceAlphabet alphabet steps) (offset + 1) before inventory nextProfile ready frame
              (fits.mono (Forecast.plan_ge record originals.length level profile)) tailAvailable
              (children_tail safe) memos valid bounded paddedKnown
          have reads : ChildrenReads formulas solver base (.unselected (value := value) offset found rest) memos final :=
            .unselected (value := value) (absent := found) (rest := rest) restReads
          refine ⟨value :: results, after, next, final, .unselected offset found rest, reads,
            SourceCurrentConstrainedCapEditReceipt.children reads populated allowed ready available safe valid returned,
            returned, finalFits, ?_, ?_⟩
          · change Carrier (fun guard => guard ∈ advanceAlphabet alphabet ((values.length + 1) * steps))
              after.checked.native.machine.heap
            rw [← advance_scan alphabet values.length steps]
            exact restKnown
          · simp only [Worker.children, found, done, SourceCurrentAllocatedSharedEditWorker.Outcome.bind]
      | some edits =>
          have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
          have supported := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
            by simpa only [Populated] using populated) _ _ member
          have selected : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
          have firstSafe := safe 0 _ (by simpa using found) value rfl
          obtain ⟨result, middle, currentInventory, current, first, firstReads, firstReceipt,
              firstFrame, firstFits, firstKnown, firstDone⟩ :=
            node alphabet edits value before inventory profile (sizes _ _ member) supported.1 supported.2 selected
              ready frame fits (available _ List.mem_cons_self) firstSafe
              memos valid later room knownAlphabet
          obtain ⟨results, after, next, final, rest, restReads, _receipt, returned, finalFits, restKnown, done⟩ :=
            ih (advanceAlphabet alphabet steps) (offset + 1) middle currentInventory nextProfile firstReceipt.ready firstFrame firstFits
              (fun original present => firstReceipt.effects.keeps.available original (tailAvailable original present))
              (children_tail safe) current firstReceipt.globals.valid bounded firstKnown
          have reads : ChildrenReads formulas solver base (.selected offset found first rest) memos final :=
            .selected (found := found) (first := first) (rest := rest) firstReads restReads
          refine ⟨result :: results, after, next, final, .selected offset found first rest, reads,
            SourceCurrentConstrainedCapEditReceipt.children reads populated allowed ready available safe valid returned,
            returned, finalFits, ?_, ?_⟩
          · change Carrier (fun guard => guard ∈ advanceAlphabet alphabet ((values.length + 1) * steps))
              after.checked.native.machine.heap
            rw [← advance_scan alphabet values.length steps]
            exact restKnown
          · simp only [Worker.children, found, firstDone, SourceCurrentAllocatedSharedEditWorker.Outcome.bind, done]

/-- Ordered raw rows use their original child limits and retain each exact constructor return. -/
theorem rows
    (alphabet : List Guard) (ceiling : Profile)
    (node : NodeComplete (bits := bits) formulas solver record originals base level ceiling)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (limit : Nat) (edges : List (EdgeValue Symbol Guard)) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile : Profile)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (resident : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (widths : ∀ edge ∈ edges, edge.children.length ≤ limit) (limitFits : limit ≤ Forecast.scalar profile)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (bounded : Le (Forecast.scan (Forecast.rowStep record originals.length level limit) edges.length profile) ceiling)
    (room : Room bits ceiling)
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ results after next final, ∃ actual : EditRows record originals entries edges before results after,
      RowsReads formulas solver base actual memos final ∧
      RowsReceipt formulas solver next record originals base edges before results after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.scan (Forecast.rowStep record originals.length level limit) edges.length profile) after.checked ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet
        (edges.length * (limit * nodeBound record originals.length ceiling level))) after.checked.native.machine.heap ∧
      Worker.rows (Worker.edit record originals (editFuel level)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
        (Forecast.stageFuel record originals.length ceiling)) entries edges before = .done results after := by
  induction edges generalizing alphabet before inventory profile memos with
  | nil =>
      have reads : RowsReads formulas solver base (EditRows.nil (record := record) (originals := originals)
          (entries := entries) (state := before)) memos memos := .nil
      exact ⟨[], before, inventory, memos, .nil, reads,
        SourceCurrentConstrainedCapEditReceipt.rows reads populated allowed ready resident safe valid frame,
        frame, fits, by simpa only [List.length_nil, Nat.zero_mul,
          SourceCurrentNativeGuardAlphabet.advance_zero] using knownAlphabet, rfl⟩
  | cons edge edges ih =>
      let steps := nodeBound record originals.length ceiling level
      let rowSteps := limit * steps
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
          childFrame, childFits, childKnown, childDone⟩ :=
        children formulas solver record originals base level alphabet ceiling node entries sizes 0 edge.children before
          inventory profile populated allowed ready frame fits available (safe edge List.mem_cons_self)
          memos valid childBounds room knownAlphabet
      have paddedFits : Fits childrenProfile middle.checked := childFits.mono
        (Forecast.scan_count_mono _ (Forecast.plan_ge record originals.length level)
          (widths edge List.mem_cons_self) profile)
      have valueLength : values.length ≤ limit := by
        rw [children_length childrenActual]
        exact widths edge List.mem_cons_self
      have field := (ready.checked.good.fields edge.entry.key edge original).grows childReceipt.effects.grows
      have built := SourceCurrentEditFrame.edge childrenProfile limit childFrame paddedFits childReceipt.ready
        edge.entry.key.symbol edge.entry.key.constraint values field childReceipt.available valueLength
      let result := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap
      have edgeFrame : Frame formulas solver childInventory (advanceHeap middle result.2).checked := built.1
      have edgeReady : Ready formulas solver childInventory record originals base (advanceHeap middle result.2) := built.2.2.1
      have edgeEffects := built.2.2.2.1
      have limitAfter : limit ≤ Forecast.scalar childrenProfile := Nat.le_trans limitFits
        (Forecast.scalar_mono (Forecast.scan_ge _ (Forecast.plan_ge record originals.length level) limit profile))
      have edgeFits : Fits nextProfile (advanceHeap middle result.2).checked :=
        built.2.1.mono (Forecast.stage_constructor_profile record originals.length childrenProfile limitAfter)
      have paddedKnown : Carrier (fun guard => guard ∈ advanceAlphabet alphabet rowSteps)
          middle.checked.native.machine.heap := fun key edge found =>
        SourceCurrentNativeGuardAlphabet.advance_count_mono alphabet
          (Nat.mul_le_mul_right steps (widths _ List.mem_cons_self)) (childKnown key edge found)
      have guardKnown : edge.entry.key.constraint ∈ advanceAlphabet alphabet rowSteps :=
        SourceCurrentNativeGuardAlphabet.mem_advance_of_mem (knownAlphabet _ _ original) rowSteps
      have edgeKnown : Carrier (fun guard => guard ∈ advanceAlphabet alphabet rowSteps) result.2 :=
        SourceEqualityAnnotationHeap.run _ _ (SourceEqualityAnnotationHeap.makeEdge _ _ _ _ guardKnown)
          _ paddedKnown
      have kept := childReceipt.effects.keeps.trans edgeEffects.keeps
      have edgeValid := SourceQueryUnfoldMemo.valid_grows middle.checked.native.machine.heap result.2
        childReceipt.ready.checked.semantic edgeEffects.keeps current childReceipt.globals.valid
      have nextLimit : limit ≤ Forecast.scalar nextProfile := Nat.le_trans limitFits
        (Forecast.scalar_mono (Forecast.rowStep_ge record originals.length level limit profile))
      obtain ⟨results, after, next, final, rest, restReads, _receipt, returned, finalFits, restKnown, done⟩ :=
        ih (advanceAlphabet alphabet rowSteps) (advanceHeap middle result.2) childInventory nextProfile edgeReady edgeFrame edgeFits
          (fun original member => InternedEdgeResidency.edge_grows _ _ kept.growth original
            (resident original (List.mem_cons_of_mem _ member)))
          (fun original member => safe original (List.mem_cons_of_mem _ member))
          (fun original member => widths original (List.mem_cons_of_mem _ member)) nextLimit current edgeValid bounded edgeKnown
      have made : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
          middle.checked.native.machine.heap = (result.1, result.2) := rfl
      let actual : EditRows record originals entries (edge :: edges) before (result.1 :: results) after :=
        .cons childrenActual made rest
      have reads : RowsReads formulas solver base actual memos final :=
        .cons (children := childrenActual) (rebuilt := made) (rest := rest) childReads restReads
      refine ⟨result.1 :: results, after, next, final, actual, reads,
        SourceCurrentConstrainedCapEditReceipt.rows reads populated allowed ready resident safe valid returned,
        returned, finalFits, ?_, ?_⟩
      · change Carrier (fun guard => guard ∈ advanceAlphabet alphabet ((edges.length + 1) * rowSteps))
          after.checked.native.machine.heap
        rw [← advance_scan alphabet edges.length rowSteps]
        exact restKnown
      · simp only [Worker.rows, childDone, SourceCurrentAllocatedSharedEditWorker.Outcome.bind, Worker.work, made, done]

end MicroCFTA.SourceCurrentEditGuardScans
