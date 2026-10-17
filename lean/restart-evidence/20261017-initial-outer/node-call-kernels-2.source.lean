import MicroCFTA.SourceCurrentNodeCallNumeric
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.InternedFreshOrdinaryStoredCosts
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.NodeCallNumericKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) cached allocation
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by simpa only [expression, SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards,
      List.nil_append, List.append_nil] using member) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩

private theorem no_cap (depth : Nat) : ¬Cap depth value := by
  intro bounded
  cbv at bounded
  cases bounded with
  | plain _ annotated =>
      cases annotated with
      | mu _ _ _ _ body =>
          cases body with
          | node _ _ _ _ annotations _ =>
              have rejected := annotations _ List.mem_cons_self
              change SourceMemoGate.plain annotation = true at rejected
              have invalid : SourceMemoGate.plain annotation = false := by cbv
              rw [invalid] at rejected
              cases rejected

private theorem initial_frame (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before (bits + 2)) :=
  Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl

private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem context (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (caller width) EndpointMemoGateTrace.empty := by
  have frame : Frame formulas solver inventory (before width) :=
    Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
  exact ⟨(initial width).1, frame.admitted,
    SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver (before width)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty,
    SourceCurrentMemoMergeEffects.stored_empty heap,
    (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty
      (SourceEqualityPCSGuard.holds formulas solver) ambient),
    SourceCurrentEmptinessMemo.empty_correct formulas solver heap, EndpointMemoGateTrace.empty_valid heap,
    SourceCurrentAllocatedMuRebuild.constructed expression value heap constructed⟩


private def request : SourceCurrentAllocatedPartialState.NodeRequest := ⟨.contradiction, value⟩
private theorem inherited (width : Nat) :
    SourceEqualityConstraintAllocation.Ready (before width).operations.constraints request.inherited :=
  ⟨trivial, by intro originals impossible; cases impossible⟩
private theorem terminal : SourceCurrentNodeTerminalNumeric.Terminal request.value := by
  cbv
  exact .binder
private def running (width : Nat) :=
  (SourceCurrentAllocatedPartialState.beginNode request (caller width)).2.2
private theorem started (width : Nat) : SourceCurrentAllocatedPartialState.beginNode request (caller width) =
    (0, .evaluate request, running width) := by
  have first := (SourceCurrentAllocatedPartialMemoSound.beginNode_fresh request (caller width) (by rfl)).1
  exact Prod.ext (congrArg Prod.fst first) (Prod.ext (congrArg (fun observed => observed.2.1) first) rfl)
private theorem running_table (width : Nat) :
    (running width).nodeResults.table request.key = some 0 := by
  simp only [running, caller, SourceCurrentAllocatedPartialState.initial,
    SourceCurrentAllocatedPartialState.beginNode, FlatMemoThunk.empty, FlatMemoThunk.lookupOrInsert,
    FlatMemoThunk.demand, FlatMemoThunk.setStatus, put, ite_true]
private theorem finish_table (handle : Nat) (result : Value Symbol Guard)
    (state : FlatMemoThunk.State SourceCurrentAllocatedPartialState.NodeKey
      SourceCurrentAllocatedPartialState.NodeRequest (Value Symbol Guard)) :
    (FlatMemoThunk.finish handle result state).table = state.table := by
  cases found : state.cells handle with
  | none => simp only [FlatMemoThunk.finish, found]
  | some cell => cases cell with
    | mk original phase => cases phase <;> simp only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus]

/-- A constructed constrained Mu completes cold and reuses its exact whole returned caller. -/
theorem constructed_cold_warm
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧
    ∃ result after,
      SourceCurrentNodeCallNumeric.Receipt formulas solver inventory profile 0 request (caller 2)
        EndpointMemoGateTrace.empty result after ∧
      after.nodeResults.cells 0 = some ⟨request, .returned result⟩ ∧
      SourceCurrentNodeCallNumeric.Receipt formulas solver inventory profile 0 request after
        EndpointMemoGateTrace.empty result after := by
  obtain ⟨result, receipt, returned⟩ := SourceCurrentNodeCallNumeric.terminal_evaluated
    formulas solver inventory 0 request (caller 2) EndpointMemoGateTrace.empty
    (context 2 formulas solver) (initial_frame 0 formulas solver) profile (initial_fits 2)
    (inherited 2) (initial 2).2.1 terminal (started 2)
  let after := SourceCurrentAllocatedPartialState.finishNode 0 result (running 2)
  have table : after.nodeResults.table request.key = some 0 := by
    change (FlatMemoThunk.finish 0 result (running 2).nodeResults).table request.key = some 0
    rw [finish_table]
    exact running_table 2
  have warm := SourceCurrentAllocatedPartialState.beginNode_ready request request after 0 result table returned
  have afterInherited : SourceEqualityConstraintAllocation.Ready after.checked.operations.constraints request.inherited :=
    ⟨trivial, by intro originals impossible; cases impossible⟩
  have afterAvailable : Available after.checked.native.machine.heap request.value :=
    receipt.post.effects.keeps.available value (initial 2).2.1
  have replay := (SourceCurrentNodeCallNumeric.ready formulas solver inventory 0 request after EndpointMemoGateTrace.empty
    receipt.post.context receipt.frame profile receipt.fits afterInherited afterAvailable warm).2
  exact ⟨no_cap, result, after, receipt, returned, replay⟩

/-- The sound post-publication node caller retains its exact busy fault with no Room. -/
theorem constructed_busy_no_room
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (running 2) EndpointMemoGateTrace.empty ∧
    ¬SourceCurrentAllocatedNativeResourceForecast.Room 0 profile ∧
    ∀ f g s r e p h m c n,
      SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n 0 request (running 2) =
        .failed (.nodeMemo 0 .busy) (running 2) := by
  obtain ⟨initial, _owner, _, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start
    formulas solver (context 2 formulas solver) (inherited 2) (initial 2).2.1 (started 2)
  have observed := SourceCurrentAllocatedPartialState.beginNode_busy request request (running 2) 0 (running_table 2) cell
  have noRoom : ¬SourceCurrentAllocatedNativeResourceForecast.Room 0 profile := by
    intro room
    have impossible : profile.nodes < 1 := room.1
    have positive : 1 ≤ profile.nodes := by cbv
    omega
  exact ⟨initial, noRoom, fun f g s r e p h m c n =>
    SourceCurrentAllocatedPartialWorker.nodeCall_busy f g s r e p h m c n 0 request (running 2) (running 2) 0 observed⟩

end MicroCFTA.NodeCallNumericKernels
#check @MicroCFTA.NodeCallNumericKernels.constructed_cold_warm
#print axioms MicroCFTA.NodeCallNumericKernels.constructed_cold_warm
#check @MicroCFTA.NodeCallNumericKernels.constructed_busy_no_room
#print axioms MicroCFTA.NodeCallNumericKernels.constructed_busy_no_room
