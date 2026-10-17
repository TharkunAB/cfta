import MicroCFTA.SourceCurrentEditScans
import MicroCFTA.SourceCurrentLeafNumeric


/-!
# Initial numeric completion for finite mixed node edits

The finite trie size controls the selected child induction. A recursive
input first constructs its actual ordinary Head. Original row and child
widths are fixed before each scan. One initial final-profile room test
supplies every reached leaf. No future range or completed edit is supplied.
-/
namespace MicroCFTA.SourceCurrentEditNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects (NodeReceipt)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentEditScans (NodeComplete editFuel)
namespace Forecast
export SourceCurrentConstrainedCapEditForecast
  (scalar scalar_mono stageProfile stageFuel stage_ge stageFuel_mono stage_constructor_profile stage_leaf_profile
    stage_leaf_fuel stage_leaf_reserved stage_head_profile stage_head_fuel planProfile plan_ge plan_stage
    plan_succ scan scan_ge scan_count_mono rowStep rowStep_ge)
end Forecast
namespace Worker
export SourceCurrentAllocatedSharedEditWorker (edit rows work head leaf lift Outcome)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {bits : Nat}

private theorem child_size {entries : List (Int × Edits EqualityNormalize.Path)} {level : Nat}
    (small : sizeOf (Edits.editBelow entries) ≤ level + 1) :
    ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level := by
  intro index child member
  have inside := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec] at inside
  simp only [Edits.editBelow.sizeOf_spec] at small
  omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem ordinary (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (base : Heap) (level : Nat)
    (node : NodeComplete (bits := bits) formulas solver record originals base level)
    (entries : List (Int × Edits EqualityNormalize.Path))
    (sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : SharedState (bits + 2)) (inventory : Inventory) (profile : Profile)
    (populated : Populated (.editBelow entries)) (nonempty : HasLeaf (.editBelow entries))
    (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits (Forecast.stageProfile record originals.length profile) before.checked)
    (available : Available before.checked.native.machine.heap (.node entry edges depth free))
    (safe : Safe (.editBelow entries) (.node entry edges depth free))
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (room : Room bits (Forecast.planProfile record originals.length (level + 1) profile)) :
    ∃ result after next final, ∃ actual : EditNode record originals (.editBelow entries)
        (.node entry edges depth free) before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base (.node entry edges depth free) before result after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.planProfile record originals.length (level + 1) profile) after.checked ∧
      Worker.edit record originals (editFuel level + 1)
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length (level + 1) profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length (level + 1) profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length (level + 1) profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length (level + 1) profile))
        (Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length (level + 1) profile))
        (.editBelow entries) (.node entry edges depth free) before = .done result after := by
  let start := Forecast.stageProfile record originals.length profile
  let width := Forecast.scalar start
  let ceiling := Forecast.planProfile record originals.length (level + 1) profile
  let allRows := Forecast.scan (Forecast.rowStep record originals.length level width) width start
  have resident := InternedEdgeResidency.resident_edges before.checked.native.machine.heap
    ready.checked.semantic.ready.semantic.1.normal.facts.linked _ available.resident
  have mass := InternedValueMassHeap.available before.checked.native.machine.heap fits.stored _ available
  have scalar := SourceCurrentConstrainedCapTargetForecast.scalar_mass start
  have length : edges.length ≤ width := by
    have counts := InternedValueMass.edges_eq_length_sum edges
    simp only [InternedValueMass.value] at mass
    change 1 + InternedValueMass.edges edges ≤ start.mass at mass
    change start.mass ≤ width at scalar
    omega
  have widths : ∀ edge ∈ edges, edge.children.length ≤ width := by
    intro edge member
    have small := InternedValueMassHeap.resident before.checked.native.machine.heap fits.stored edge (resident edge member)
    have counts := InternedValueMass.values_eq_length_sum edge.children
    rw [InternedValueMass.edge_children] at small
    change 1 + InternedValueMass.values edge.children ≤ start.mass at small
    change start.mass ≤ width at scalar
    omega
  have bounded : Le (Forecast.scan (Forecast.rowStep record originals.length level width) edges.length start) ceiling := by
    dsimp only [ceiling]
    rw [Forecast.plan_succ]
    exact (Forecast.scan_count_mono _ (Forecast.rowStep_ge record originals.length level width) length start).trans
      (Forecast.stage_ge record originals.length allRows)
  obtain ⟨rebuilt, middle, finalInventory, current, rowsActual, rowsReads, rowsReceipt,
      returned, rowsFits, rowsDone⟩ :=
    SourceCurrentEditScans.rows formulas solver record originals base level node entries sizes
      width edges before inventory start ceiling populated allowed ready frame fits resident (ordinary_rows safe)
      widths (Nat.le_refl _) memos valid bounded room
  have paddedFits : Fits allRows middle.checked := rowsFits.mono
    (Forecast.scan_count_mono _ (Forecast.rowStep_ge record originals.length level width) length start)
  have resultLength : rebuilt.length ≤ width := by
    rw [SourceCurrentConstrainedCapEditReceipt.rows_length rowsActual]
    exact length
  have made := SourceCurrentEditFrame.node allRows width returned paddedFits rowsReceipt.ready
    rebuilt rowsReceipt.available resultLength
  let result := run (makeNode rebuilt) middle.checked.native.machine.heap
  have nextFrame : Frame formulas solver finalInventory (advanceHeap middle result.2).checked := made.1
  have numeric : Fits ceiling (advanceHeap middle result.2).checked := by
    have widthFits : width ≤ Forecast.scalar allRows := Forecast.scalar_mono
      (Forecast.scan_ge _ (Forecast.rowStep_ge record originals.length level width) width start)
    have stage := made.2.1.mono (Forecast.stage_constructor_profile record originals.length allRows widthFits)
    exact stage
  have reads : NodeReads formulas solver base
      (EditNode.ordinary (entry := entry) (depth := depth) (free := free) rowsActual rfl) memos current := .ordinary (actual := rowsActual) (built := rfl) rowsReads
  refine ⟨result.1, advanceHeap middle result.2, finalInventory, current, .ordinary rowsActual rfl, reads,
    SourceCurrentConstrainedCapEditReceipt.node reads populated nonempty allowed ready available safe valid nextFrame,
    nextFrame, numeric, ?_⟩
  change (Worker.rows (Worker.edit record originals (editFuel level)
    (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
    (Forecast.stageFuel record originals.length ceiling) (Forecast.stageFuel record originals.length ceiling)
    (Forecast.stageFuel record originals.length ceiling)) entries edges before).bind
      (fun rebuilt middle => Worker.work (makeNode rebuilt) middle) = .done result.1 (advanceHeap middle result.2)
  rw [rowsDone]
  rfl

/-- Initial captured facts construct every supported finite node trie by size-bounded induction. -/
theorem node_complete (level : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
    (known : Values base originals)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths) :
    NodeComplete (bits := bits) formulas solver record originals base level := by
  induction level with
  | zero =>
      intro edits input before inventory profile small
      cases edits <;> simp only [Edits.editAt.sizeOf_spec, Edits.editBelow.sizeOf_spec] at small <;> omega
  | succ level ih =>
      intro edits input before inventory profile small populated nonempty allowed ready frame fits available safe memos valid room
      let ceiling := Forecast.planProfile record originals.length (level + 1) profile
      let fuel := Forecast.stageFuel record originals.length ceiling
      cases edits with
      | editAt path =>
          have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
          have closed : input.free = [] := by
            simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using safe [] path (by simp [SourceEqualityEditLeafPaths.leaves])
          have reserved := Forecast.stage_leaf_reserved record originals.length bits path (before.targets path).isSome
            (Le.refl profile) member (room.mono (Forecast.plan_stage record originals.length (level + 1) profile))
          obtain ⟨result, after, next, final, receipt, returned, finalFits, done⟩ :=
            SourceCurrentLeafNumeric.complete formulas solver inventory record originals base
              before profile ready frame fits known domains coherent active path member input available closed
              memos valid reserved
          have branch := Forecast.stage_leaf_profile record originals.length path (before.targets path).isSome profile member
          have numeric := finalFits.mono (branch.trans (Forecast.plan_stage record originals.length (level + 1) profile))
          have enough := Nat.le_trans (Forecast.stage_leaf_fuel record originals.length path (before.targets path).isSome profile member)
            (Forecast.stageFuel_mono record originals.length (Forecast.plan_ge record originals.length (level + 1) profile))
          have lifted := SourceCurrentAllocatedSharedTargetWorkerStability.leaf_done_stable done enough enough enough enough enough
          have reads : NodeReads formulas solver base (.leaf receipt.actual) memos final := .leaf receipt
          refine ⟨result, after, next, final, .leaf receipt.actual, reads,
            SourceCurrentConstrainedCapEditReceipt.node reads populated nonempty allowed ready available safe valid returned,
            returned, numeric, ?_⟩
          simp only [editFuel, Worker.edit, Worker.leaf, Worker.lift, lifted]
      | editBelow entries =>
          have sizes := child_size small
          have ordinaryCase := ordinary formulas solver record originals base level ih entries sizes
          have startFits := fits.mono (Forecast.stage_ge record originals.length profile)
          let original := input
          cases input with
          | empty =>
              have reads : NodeReads formulas solver base (EditNode.empty (record := record) (originals := originals)
                  (entries := entries) (state := before)) memos memos := .empty
              exact ⟨.empty, before, inventory, memos, .empty, reads,
                SourceCurrentConstrainedCapEditReceipt.node reads populated nonempty allowed ready available safe valid frame,
                frame, fits.mono (Forecast.plan_ge record originals.length (level + 1) profile), rfl⟩
          | reference name =>
              obtain ⟨path, action, member⟩ := nonempty
              have impossible := safe path action member
              cases path <;> simp only [SourceEqualityProjectionPathDomain.NodeClosed, Value.free] at impossible <;> cases impossible
          | node entry edges depth free =>
              obtain ⟨result, after, next, final, actual, reads, receipt, returned, numeric, done⟩ :=
                ordinaryCase entry edges depth free before inventory profile populated nonempty allowed ready frame startFits
                  available safe memos valid room
              exact ⟨result, after, next, final, actual, reads, receipt, returned, numeric,
                SourceCurrentAllocatedSharedEditWorkerStability.edit_done_stable done
                  (show editFuel level + 1 ≤ editFuel (level + 1) by unfold editFuel; omega)
                  (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
          | mu entry body depth ordinaryProbe | union entry members depth free =>
              have recursive : SourceEqualityRequiredGraph.Recursive original := by trivial
              have closed := recursive_closed recursive nonempty safe
              obtain ⟨exposed, heap, head, _kept, exposedAvailable, exposedClosed, exposedOrdinary⟩ :=
                SourceEqualityRequiredHead.complete original before.checked.native.machine.heap ready.checked.semantic.ready available closed
              have first := SourceCurrentEditFrame.head profile frame fits ready head available closed
              obtain ⟨current, headReads, headValid, retained, query⟩ := SourceCurrentRequiredQueryMemos.head_memos
                head ready.checked.semantic ready.checked.costs available memos valid
              have headGlobal : SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current :=
                ⟨first.2.2.2.1.keeps, first.1.ready.semantic, first.1.ready.costs, headValid, retained, query⟩
              have exposedFits := first.2.1.mono (Forecast.stage_head_profile record originals.length profile)
              have exposedReady := first.2.2.1
              have exposedSafe := closed_safe (.editBelow entries) exposed heap exposedReady.checked.semantic exposedAvailable exposedClosed
              have solve : ∃ result after next final, ∃ actual : EditNode record originals (.editBelow entries) exposed
                  (advanceHeap before heap) result after,
                  NodeReads formulas solver base actual current final ∧
                  NodeReceipt formulas solver next record originals base exposed (advanceHeap before heap) result after current final ∧
                  Frame formulas solver next after.checked ∧ Fits ceiling after.checked ∧
                  Worker.edit record originals (editFuel level + 1) fuel fuel fuel fuel fuel
                    (.editBelow entries) exposed (advanceHeap before heap) = .done result after := by
                cases exposed with
                | empty =>
                    have reads : NodeReads formulas solver base (EditNode.empty (record := record) (originals := originals)
                        (entries := entries) (state := advanceHeap before heap)) current current := .empty
                    exact ⟨.empty, advanceHeap before heap, inventory, current, .empty, reads,
                      SourceCurrentConstrainedCapEditReceipt.node reads populated nonempty allowed exposedReady exposedAvailable
                        exposedSafe headValid first.1, first.1,
                      exposedFits.mono (Forecast.plan_stage record originals.length (level + 1) profile), rfl⟩
                | node entry edges depth free =>
                    exact ordinaryCase entry edges depth free (advanceHeap before heap) inventory profile populated nonempty allowed
                      exposedReady first.1 exposedFits exposedAvailable exposedSafe current headValid room
                | reference | mu | union => cases exposedOrdinary
              obtain ⟨result, after, next, final, actual, reads, _receipt, returned, numeric, done⟩ := solve
              have allReads : NodeReads formulas solver base (.recursive recursive head actual) memos final :=
                .recursive (recursive := recursive) (head := head) (body := actual) headReads headGlobal reads
              have enough : SourceCurrentEditFrame.headFuel profile ≤ fuel :=
                Nat.le_trans (Forecast.stage_head_fuel record originals.length profile)
                  (Forecast.stageFuel_mono record originals.length (Forecast.plan_ge record originals.length (level + 1) profile))
              have headDone : Worker.head fuel original before = .done exposed (advanceHeap before heap) := by
                have replay := SourceCurrentProjectionNumericReplay.head_replay first.2.2.2.2.2.2 fuel enough
                simp only [Worker.head, replay]
              refine ⟨result, after, next, final, .recursive recursive head actual, allReads,
                SourceCurrentConstrainedCapEditReceipt.node allReads populated nonempty allowed ready available safe valid returned,
                returned, numeric, ?_⟩
              have sameFuel : editFuel (level + 1) = (editFuel level + 1) + 1 := by unfold editFuel; omega
              rw [sameFuel]
              change (Worker.head fuel original before).bind
                (fun exposed middle => Worker.edit record originals (editFuel level + 1) fuel fuel fuel fuel fuel
                  (.editBelow entries) exposed middle) = .done result after
              rw [headDone]
              exact done

end MicroCFTA.SourceCurrentEditNumeric
