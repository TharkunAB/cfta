import MicroCFTA.SourceCurrentEditListNumeric
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedSharedEditRanges

/-!
# Actual edit range plans from initial numeric reservations

The existing numeric producers construct complete prefix executions.
Worker uniqueness identifies every alternative completed prefix with the
constructed prefix. Its returned Frame and reservation supply the next
word checks. Recursive heads use their actual returned constructor heap.

The result retains the original finite trie and captured class forest.
It adds no ordinary-tree restriction or returned-state assumption.
-/
namespace MicroCFTA.SourceCurrentEditListNumericRanges
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditRanges
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
namespace Forecast
export SourceCurrentConstrainedCapEditForecast
  (scalar stageProfile stage_ge stage_leaf_reserved stage_head_profile planProfile plan_ge plan_stage
    plan_succ scan scan_ge scan_child scan_count_mono rowStep rowStep_ge)
end Forecast
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "requestNode" => SourceRecursiveIntersectionCode.requestNode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem target_unique {values paths before memo first after saved second later current}
    (one : SourceCurrentAllocatedTargetGraph.Target (width := bits + 2) values paths before memo first after saved)
    (two : SourceCurrentAllocatedTargetGraph.Target values paths before memo second later current) :
    first = second ∧ after = later ∧ saved = current := by
  obtain ⟨a, ha⟩ := SourceCurrentAllocatedTargetWorkerCompletion.target_uniform one
  obtain ⟨b, hb⟩ := SourceCurrentAllocatedTargetWorkerCompletion.target_uniform two
  exact SourceCurrentAllocatedTargetWorker.Outcome.done.inj
    ((ha (max a b) (Nat.le_max_left _ _)).symm.trans (hb (max a b) (Nat.le_max_right _ _)))

private theorem operand_unique {values path before memo first after saved second later current}
    (one : SourceCurrentAllocatedTargetGraph.Operand (width := bits + 2) path values before memo first after saved)
    (two : SourceCurrentAllocatedTargetGraph.Operand path values before memo second later current) :
    first = second ∧ after = later ∧ saved = current :=
  target_unique (.nonempty (.nil one)) (.nonempty (.nil two))

private theorem fold_unique {values seed paths before memo first after saved second later current}
    (one : SourceCurrentAllocatedTargetGraph.Fold (width := bits + 2) values seed paths before memo first after saved)
    (two : SourceCurrentAllocatedTargetGraph.Fold values seed paths before memo second later current) :
    first = second ∧ after = later ∧ saved = current :=
  target_unique (.nonempty one) (.nonempty two)

private theorem node_unique {record originals edits input before first after second later}
    (one : EditNode (width := bits + 2) record originals edits input before first after)
    (two : EditNode record originals edits input before second later) : first = second ∧ after = later := by
  obtain ⟨a, ha⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete one)
  obtain ⟨b, hb⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete two)
  exact SourceCurrentAllocatedSharedEditWorker.Outcome.done.inj
    ((ha (max a b) (Nat.le_max_left _ _)).symm.trans (hb (max a b) (Nat.le_max_right _ _)))

private theorem children_unique {record originals entries index inputs before first after second later}
    (one : EditChildren (width := bits + 2) record originals entries index inputs before first after)
    (two : EditChildren record originals entries index inputs before second later) : first = second ∧ after = later := by
  obtain ⟨a, ha⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete one)
  obtain ⟨b, hb⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete two)
  exact SourceCurrentAllocatedSharedEditWorker.Outcome.done.inj
    ((ha (max a b) (Nat.le_max_left _ _)).symm.trans (hb (max a b) (Nat.le_max_right _ _)))

private theorem force_unique {record values path before first after second later}
    (one : SourceCurrentAllocatedSharedTargetForce.Force (width := bits + 2) record values path before first after)
    (two : SourceCurrentAllocatedSharedTargetForce.Force record values path before second later) :
    first = second ∧ after = later := by
  obtain ⟨p, h, m, s, n, ha⟩ := SourceCurrentAllocatedSharedTargetWorkerCompletion.force_complete one
  obtain ⟨q, i, k, t, j, hb⟩ := SourceCurrentAllocatedSharedTargetWorkerCompletion.force_complete two
  exact SourceCurrentAllocatedSharedTargetWorker.Outcome.done.inj
    ((ha (max p q) (max h i) (max m k) (max s t) (max n j)
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (hb (max p q) (max h i) (max m k) (max s t) (max n j)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

private theorem request_ranges
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before : Checked (bits + 2)} {profile : Profile}
    (frame : Frame formulas solver inventory before) (fits : Fits profile before) (room : Room bits profile)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right) (leftClosed : left.free = []) (rightClosed : right.free = []) :
    WordRanges (.code (requestNode emptyDomain left right)) before := by
  have facts := frame.ready.good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left _ facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right _ facts.coherent rightAvailable rightClosed
  have capacity := fits.room room
  exact (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before frame.ready.good
    frame.ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable
    capacity.1 capacity.2.1 capacity.2.2).1

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem tail_domains {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

private theorem target_fold_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int)) (inventory : Inventory)
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ seed :: paths, Domain path values)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapTargetForecast.Reserved bits values.length seed paths profile) :
    SourceCurrentAllocatedTargetGraph.FoldRanges values seed paths before memo := by
  induction paths generalizing inventory before memo profile memos with
  | nil => trivial
  | cons path paths ih =>
      obtain ⟨head, middle, current, nextMemos, headActual, first, headFrame, headFits, _headDone⟩ :=
        SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory path values before memo profile
          frame fits available (domains path (by simp)) physicalStored covered memos valid
      refine ⟨?_, ?_⟩
      · intro other reached saved actual
        have same := operand_unique actual headActual
        rw [same.2.1, same.2.2]
        exact ih inventory middle current (SourceCurrentConstrainedCapTargetForecast.operand path values.length profile)
          headFrame headFits first.originals (tail_domains domains) first.stored first.covered
          nextMemos first.globals reserved.1
      · intro other reached saved tail later final actual restActual
        have same := operand_unique actual headActual
        have restAligned : SourceCurrentAllocatedTargetGraph.Fold values seed paths middle current tail later final := by
          simpa only [← same.2.1, ← same.2.2] using restActual
        obtain ⟨next, result, after, retained, globals, chosen, _reads, rest, returned, finalFits, _done⟩ :=
          SourceCurrentTargetNumeric.fold_complete formulas solver values seed paths inventory middle current
            (SourceCurrentConstrainedCapTargetForecast.operand path values.length profile)
            headFrame headFits first.originals (tail_domains domains) first.stored first.covered
            nextMemos first.globals reserved.1
        have tailSame := fold_unique restAligned chosen
        rw [same.1, tailSame.1, tailSame.2.1]
        exact request_ranges returned finalFits reserved.2 head result
          (rest.effects.keeps.available head first.available) rest.available first.closed rest.closed

private theorem leaf_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : Heap) (before : SharedState (bits + 2)) (profile : Profile)
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (known : Values base originals) (domains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapSharedForecast.LeafReserved bits originals.length
      (SourceEqualityClassTarget.operandPaths record.paths path) (before.targets path).isSome profile) :
    SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals path input before := by
  refine ⟨?_, ?_⟩
  · intro absent
    have targetReserved : SourceCurrentConstrainedCapTargetForecast.TargetReserved bits originals.length
        (SourceEqualityClassTarget.operandPaths record.paths path) profile := by
      simpa only [absent, Option.isSome, SourceCurrentConstrainedCapSharedForecast.forceReserved_miss] using reserved.1
    have operandDomains := SourceCurrentTargetPathComplete.operand_domains record originals domains path
    cases computed : SourceEqualityClassTarget.operandPaths record.paths path with
    | nil => trivial
    | cons seed rest =>
        apply target_fold_ranges formulas solver originals seed rest inventory before.checked before.memo profile
          frame fits (fun value included => ready.captured.available value (known value included))
          (by simpa only [computed] using operandDomains) ready.stored ready.covered memos valid
        simpa only [computed, SourceCurrentConstrainedCapTargetForecast.TargetReserved] using targetReserved
  · intro target middle actual
    obtain ⟨chosen, reached, next, current, first, returned, finalFits, _done⟩ :=
      SourceCurrentForceNumeric.complete formulas solver inventory record originals base before profile
        ready frame fits known domains coherent active path member memos valid reserved.1
    have same := force_unique actual first.actual
    rw [same.1, same.2]
    exact request_ranges returned finalFits reserved.2 chosen input first.available
      (first.effects.keeps.available input available) first.closed closed

private def NodePlan (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (base : Heap) (level : Nat) : Prop :=
  ∀ (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile : Profile),
    sizeOf edits ≤ level → Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Frame formulas solver inventory before.checked →
    Fits profile before.checked → Available before.checked.native.machine.heap input → Safe edits input →
    ∀ (memos : Memos), Valid before.checked.native.machine.heap memos →
    Room bits (Forecast.planProfile record originals.length level profile) →
    NodeRanges record originals edits input before

section Trie
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals)
variable (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
include known domains coherent active

private theorem children_ranges (level : Nat)
    (plan : NodePlan (bits := bits) formulas solver record originals base level)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (offset : Nat) (values : List (Value Symbol Guard)) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile ceiling : Profile)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (bounded : Le (Forecast.scan (Forecast.planProfile record originals.length level) values.length profile) ceiling)
    (room : Room bits ceiling) : ChildrenRanges record originals entries offset values before := by
  induction values generalizing offset before inventory profile memos with
  | nil => exact .nil
  | cons value values ih =>
      let nextProfile := Forecast.planProfile record originals.length level profile
      have later : Le nextProfile ceiling :=
        (Forecast.scan_child (Forecast.planProfile record originals.length level)
          (Forecast.plan_ge record originals.length level) (by simp only [List.length_cons]; omega) profile).trans bounded
      have tailAvailable : Values before.checked.native.machine.heap values :=
        fun original member => available original (List.mem_cons_of_mem _ member)
      cases found : SourceEqualityNeededMap.lookup (offset : Int) entries with
      | none =>
          exact .unselected offset found
            (ih (offset + 1) before inventory nextProfile ready frame
              (fits.mono (Forecast.plan_ge record originals.length level profile)) tailAvailable
              (children_tail safe) memos valid bounded)
      | some edits =>
          have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
          have supported := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
            by simpa only [Populated] using populated) _ _ member
          have selected : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
          have firstSafe := safe 0 _ (by simpa using found) value rfl
          have firstPlan := plan edits value before inventory profile (sizes _ _ member) supported.1 supported.2
            selected ready frame fits (available _ List.mem_cons_self) firstSafe memos valid (room.mono later)
          refine .selected offset found firstPlan ?_
          intro result middle actual
          obtain ⟨chosen, reached, next, current, first, _reads, receipt, returned, finalFits, _done⟩ :=
            SourceCurrentEditNumeric.node_complete level formulas solver record originals base known domains coherent active
              edits value before inventory profile (sizes _ _ member) supported.1 supported.2 selected
              ready frame fits (available _ List.mem_cons_self) firstSafe memos valid (room.mono later)
          have same := node_unique actual first
          rw [same.2]
          exact ih (offset + 1) reached next nextProfile receipt.ready returned finalFits
            (fun original present => receipt.effects.keeps.available original (tailAvailable original present))
            (children_tail safe) current receipt.globals.valid bounded

private theorem rows_ranges (level : Nat)
    (plan : NodePlan (bits := bits) formulas solver record originals base level)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (limit : Nat) (rows : List (EdgeValue Symbol Guard)) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile ceiling : Profile)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (resident : Edges before.checked.native.machine.heap rows) (safe : RowsSafe entries rows)
    (widths : ∀ row ∈ rows, row.children.length ≤ limit) (limitFits : limit ≤ Forecast.scalar profile)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (bounded : Le (Forecast.scan (Forecast.rowStep record originals.length level limit) rows.length profile) ceiling)
    (room : Room bits ceiling) : RowsRanges record originals entries rows before := by
  induction rows generalizing before inventory profile memos with
  | nil => exact .nil
  | cons edge rows ih =>
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
      have firstPlan := children_ranges formulas solver record originals base known domains coherent active level
        plan entries sizes 0 edge.children before inventory profile ceiling populated allowed ready frame fits
        available (safe edge List.mem_cons_self) memos valid childBounds room
      refine .cons firstPlan ?_
      intro values middle actual
      have node := SourceCurrentEditNumeric.node_complete (bits := bits) level
        formulas solver record originals base known domains coherent active
      obtain ⟨chosen, reached, childInventory, current, childrenActual, _reads, receipt, returned, finalFits, _done⟩ :=
        SourceCurrentEditScans.children formulas solver record originals base level node entries sizes 0 edge.children before
          inventory profile ceiling populated allowed ready frame fits available (safe edge List.mem_cons_self)
          memos valid childBounds room
      have same := children_unique actual childrenActual
      rw [same.1, same.2]
      have paddedFits : Fits childrenProfile reached.checked := finalFits.mono
        (Forecast.scan_count_mono _ (Forecast.plan_ge record originals.length level)
          (widths edge List.mem_cons_self) profile)
      have valueLength : chosen.length ≤ limit := by
        rw [children_length childrenActual]
        exact widths edge List.mem_cons_self
      have field := (ready.checked.good.fields edge.entry.key edge original).grows receipt.effects.grows
      have built := SourceCurrentEditFrame.edge childrenProfile limit returned paddedFits receipt.ready
        edge.entry.key.symbol edge.entry.key.constraint chosen field receipt.available valueLength
      let result := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint chosen) reached.checked.native.machine.heap
      have edgeFrame : Frame formulas solver childInventory (advanceHeap reached result.2).checked := built.1
      have edgeReady : Ready formulas solver childInventory record originals base (advanceHeap reached result.2) := built.2.2.1
      have edgeEffects := built.2.2.2.1
      have limitAfter : limit ≤ Forecast.scalar childrenProfile := Nat.le_trans limitFits
        (SourceCurrentConstrainedCapEditForecast.scalar_mono
          (Forecast.scan_ge _ (Forecast.plan_ge record originals.length level) limit profile))
      have edgeFits : Fits nextProfile (advanceHeap reached result.2).checked :=
        built.2.1.mono (SourceCurrentConstrainedCapEditForecast.stage_constructor_profile record originals.length childrenProfile limitAfter)
      have kept := receipt.effects.keeps.trans edgeEffects.keeps
      have edgeValid := SourceQueryUnfoldMemo.valid_grows reached.checked.native.machine.heap result.2
        receipt.ready.checked.semantic edgeEffects.keeps current receipt.globals.valid
      have nextLimit : limit ≤ Forecast.scalar nextProfile := Nat.le_trans limitFits
        (SourceCurrentConstrainedCapEditForecast.scalar_mono (Forecast.rowStep_ge record originals.length level limit profile))
      exact ih (advanceHeap reached result.2) childInventory nextProfile edgeReady edgeFrame edgeFits
        (fun row member => InternedEdgeResidency.edge_grows _ _ kept.growth row
          (resident row (List.mem_cons_of_mem _ member)))
        (fun row member => safe row (List.mem_cons_of_mem _ member))
        (fun row member => widths row (List.mem_cons_of_mem _ member)) nextLimit current edgeValid bounded

private theorem ordinary_ranges (level : Nat)
    (plan : NodePlan (bits := bits) formulas solver record originals base level)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : SharedState (bits + 2)) (inventory : Inventory) (profile : Profile)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits (Forecast.stageProfile record originals.length profile) before.checked)
    (available : Available before.checked.native.machine.heap (.node entry rows depth free))
    (safe : Safe (.editBelow entries) (.node entry rows depth free))
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (room : Room bits (Forecast.planProfile record originals.length (level + 1) profile)) :
    NodeRanges record originals (.editBelow entries) (.node entry rows depth free) before := by
  let start := Forecast.stageProfile record originals.length profile
  let width := Forecast.scalar start
  let ceiling := Forecast.planProfile record originals.length (level + 1) profile
  let allRows := Forecast.scan (Forecast.rowStep record originals.length level width) width start
  have resident := InternedEdgeResidency.resident_edges before.checked.native.machine.heap
    ready.checked.semantic.ready.semantic.1.normal.facts.linked _ available.resident
  have mass := InternedValueMassHeap.available before.checked.native.machine.heap fits.stored _ available
  have scalar := SourceCurrentConstrainedCapTargetForecast.scalar_mass start
  have length : rows.length ≤ width := by
    have counts := InternedValueMass.edges_eq_length_sum rows
    simp only [InternedValueMass.value] at mass
    change 1 + InternedValueMass.edges rows ≤ start.mass at mass
    change start.mass ≤ width at scalar
    omega
  have widths : ∀ edge ∈ rows, edge.children.length ≤ width := by
    intro edge member
    have small := InternedValueMassHeap.resident before.checked.native.machine.heap fits.stored edge (resident edge member)
    have counts := InternedValueMass.values_eq_length_sum edge.children
    rw [InternedValueMass.edge_children] at small
    change 1 + InternedValueMass.values edge.children ≤ start.mass at small
    change start.mass ≤ width at scalar
    omega
  have bounded : Le (Forecast.scan (Forecast.rowStep record originals.length level width) rows.length start) ceiling := by
    dsimp only [ceiling]
    rw [Forecast.plan_succ]
    exact (Forecast.scan_count_mono _ (Forecast.rowStep_ge record originals.length level width) length start).trans
      (Forecast.stage_ge record originals.length allRows)
  exact .ordinary (rows_ranges formulas solver record originals base known domains coherent active level plan entries sizes
    width rows before inventory start ceiling populated allowed ready frame fits resident (ordinary_rows safe)
    widths (Nat.le_refl _) memos valid bounded room)

private theorem node_plan (level : Nat) : NodePlan (bits := bits) formulas solver record originals base level := by
  induction level with
  | zero =>
      intro edits input before inventory profile small
      cases edits <;> simp only [Edits.editAt.sizeOf_spec, Edits.editBelow.sizeOf_spec] at small <;> omega
  | succ level ih =>
      intro edits input before inventory profile small populated nonempty allowed ready frame fits available safe memos valid room
      cases edits with
      | editAt path =>
          have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
          have closed : input.free = [] := by
            simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using
              safe [] path (by simp [SourceEqualityEditLeafPaths.leaves])
          have reserved := Forecast.stage_leaf_reserved record originals.length bits path (before.targets path).isSome
            (Le.refl profile) member (room.mono (Forecast.plan_stage record originals.length (level + 1) profile))
          exact .leaf (leaf_ranges formulas solver inventory record originals base before profile ready frame fits
            known domains coherent active path member input available closed memos valid reserved)
      | editBelow entries =>
          have sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level := by
            intro index child member
            have inside := List.sizeOf_lt_of_mem member
            simp only [Prod.mk.sizeOf_spec] at inside
            simp only [Edits.editBelow.sizeOf_spec] at small
            omega
          have ordinaryCase := ordinary_ranges formulas solver record originals base known domains coherent active level ih entries sizes
          have startFits := fits.mono (Forecast.stage_ge record originals.length profile)
          let original := input
          cases input with
          | empty => exact .empty
          | reference name =>
              obtain ⟨path, action, member⟩ := nonempty
              have impossible := safe path action member
              cases path <;> simp only [SourceEqualityProjectionPathDomain.NodeClosed, Value.free] at impossible <;> cases impossible
          | node entry rows depth free =>
              exact ordinaryCase entry rows depth free before inventory profile populated allowed ready frame startFits
                available safe memos valid room
          | mu entry body depth ordinaryProbe | union entry members depth free =>
              have recursive : SourceEqualityRequiredGraph.Recursive original := by trivial
              have closed := recursive_closed recursive nonempty safe
              refine .recursive recursive ?_
              intro exposed heap actual
              have first := SourceCurrentEditFrame.head profile frame fits ready actual available closed
              obtain ⟨current, _reads, headValid, _retained, _query⟩ := SourceCurrentRequiredQueryMemos.head_memos
                actual ready.checked.semantic ready.checked.costs available memos valid
              have exposedFacts := actual.verified ready.checked.semantic.ready available closed
              have exposedFits := first.2.1.mono (Forecast.stage_head_profile record originals.length profile)
              have exposedReady := first.2.2.1
              have exposedSafe := closed_safe (.editBelow entries) exposed heap exposedReady.checked.semantic
                exposedFacts.2.1 exposedFacts.2.2.1
              cases exposed with
              | empty => exact .empty
              | node entry rows depth free =>
                  exact ordinaryCase entry rows depth free (advanceHeap before heap) inventory profile populated allowed
                    exposedReady first.1 exposedFits exposedFacts.2.1 exposedSafe current headValid room
              | reference | mu | union => cases exposedFacts.2.2.2
end Trie

/-- Initial numeric reservations derive every reached check of the literal forest edit. -/
theorem list_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : Heap) (before : SharedState (bits + 2)) (profile : Profile)
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (known : Values base originals) (domains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (edits : Edits EqualityNormalize.Path) (populated : Populated edits) (allowed : Allowed record edits)
    (values : List (Value Symbol Guard)) (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (reserved : SourceCurrentEditListNumeric.Reserved bits record originals.length edits values.length profile) :
    ListRanges record originals edits values before := by
  cases edits with
  | editAt target => trivial
  | editBelow entries =>
      let level := sizeOf (Edits.editBelow entries : Edits EqualityNormalize.Path)
      let ceiling := SourceCurrentEditListNumeric.finalProfile record originals.length (.editBelow entries) values.length profile
      have sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level := by
        intro index child member
        have smaller := List.sizeOf_lt_of_mem member
        simp only [Prod.mk.sizeOf_spec] at smaller
        dsimp only [level]
        simp only [Edits.editBelow.sizeOf_spec]
        omega
      exact children_ranges formulas solver record originals base known domains coherent active level
        (node_plan formulas solver record originals base known domains coherent active level)
        entries sizes 0 values before inventory profile ceiling populated allowed ready frame fits available safe
        memos valid (Le.refl _) reserved

end MicroCFTA.SourceCurrentEditListNumericRanges
