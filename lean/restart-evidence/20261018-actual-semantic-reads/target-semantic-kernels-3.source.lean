import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker
import MicroCFTA.SourceCurrentActualTargetSemanticReads
import MicroCFTA.SourceCurrentTargetNumeric
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryCold
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQuerySequence
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

noncomputable section

namespace MicroCFTA.TargetSemanticKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

private def top : Guard := SourceEqualityConstraintConstructors.top
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  .node [.mk ("a", .top) top [], .mk ("b", .top) top []],
  .node [.mk ("a", .top) top [], .mk ("c", .top) top []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def seedEqualities : Option EqualityNormalize.Constraints := some [[[0], [1]]]
private def seedBuild := SourceEqualityConstraintAllocation.construct seedEqualities Cache.emptyState
private def seedValue : SourceEqualityConstraintAllocation.Value := match seedBuild.1 with
  | .ok value => value
  | .error _ => .contradiction
private def seedState := SourceEqualityConstraintMemoAllocation.initial seedBuild.2
private def preparedOperations := (SourceEqualityConstraintMemoAllocation.descend seedValue 0 seedState).2
private def operations := SourceEqualityMkEdgeAllocation.emptyField preparedOperations

private theorem seed_cached : SourceEqualityGuardReadback.Cached seedEqualities := by
  have actual : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized actual

private theorem seed_constructed : seedBuild.1 = .ok seedValue := by cbv

private theorem prepared_valid : SourceEqualityConstraintMemoAllocation.Valid preparedOperations := by
  obtain ⟨value, cache, built, cacheValid, ready, _steps, _read, _classes⟩ :=
    SourceEqualityConstraintAllocation.construct_complete seedEqualities seed_cached Cache.emptyState Cache.empty_valid
  have same : value = seedValue := Except.ok.inj ((congrArg Prod.fst built).symm.trans seed_constructed)
  subst value
  have cacheSame : cache = seedBuild.2 := (congrArg Prod.snd built).symm
  subst cache
  exact (SourceEqualityConstraintMemoAllocation.descend_correct seedValue 0 seedState
    (SourceEqualityConstraintMemoAllocation.initial_valid _ cacheValid) ready).1
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good (width : Nat) : Good (before width) := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) preparedOperations
    prepared_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  have same := guarded key row found
  rw [same]
  exact loaded.2.2

private theorem originals : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact available.children left (by cbv; exact .head _)
  · exact available.children right (by cbv; exact .tail _ (.head _))

private theorem node_ready : NodeReady machine request := ⟨empty_domain machine, originals.1, originals.2⟩

private def row : EdgeValue Symbol Guard := match left with
  | .node _ (row :: _) _ _ => row
  | _ => (run (makeEdge ("unused", .top) top []) empty).1
private def candidate : Value Symbol Guard := (run (makeNode [row]) heap).1
private def nodeControl : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private noncomputable def afterFirst (width : Nat) : Checked width := (execute 8 nodeControl (before width)).state

private theorem evaluated (width : Nat) : execute 8 nodeControl (before width) = .done candidate (afterFirst width) := by
  set_option cbv.maxSteps 200000000 in cbv

private theorem candidate_absent : SourcePreparedSharedRows.read heap 3 = none := by cbv
private theorem operation_record : ∃ cell,
    operations.descents (seedValue.identity, 0) = some cell ∧
      SourceEqualityConstraintMemoAllocation.DescendGood operations.constraints (seedValue.identity, 0) cell := by
  have present : (operations.descents (seedValue.identity, 0)).isSome = true := by cbv
  cases found : operations.descents (seedValue.identity, 0) with
  | none => rw [found] at present; cases present
  | some cell => exact ⟨cell, rfl, (SourceEqualityMkEdgeAllocation.emptyField_correct preparedOperations prepared_valid).1.descents _ _ found⟩

private theorem candidate_input : SourceRecursiveIntersectionInputView.inputOf candidate = .node 3 := by cbv

private theorem candidate_outside : SourceRecursiveIntersectionInputView.inputOf candidate ∉
    SourceRecursiveIntersectionInputView.inventory heap := by
  rw [candidate_input]
  have count : heap.nodes.next = 3 := by cbv
  simp only [SourceRecursiveIntersectionInputView.inventory, count]
  decide

private theorem initial_semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap constructed

private theorem initial_guards : SourceCurrentConstrainedCapGuardHeap.Heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain heap := by
  simpa only [built, heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain expression

private theorem initial_ready (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) := by
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, heap] using InternedFreshOrdinaryCosts.closed_heap expression
  exact ⟨initial_good width, initial_semantic, costs,
    SourceCurrentAllocatedNativeScopeCache.initial_scoped width machine,
    SourceRecursiveIntersectionNative.idle_initial machine⟩

private theorem initial_caps : SourceCurrentConstrainedCap.Cap SourceCurrentConstrainedCapCheckedJointClosed.Plain 1 left ∧
    SourceCurrentConstrainedCap.Cap SourceCurrentConstrainedCapCheckedJointClosed.Plain 1 right := by
  constructor
  · cbv
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child member
    cbv at member
    cases member
  · cbv
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child member
    cbv at member
    cases member

private theorem initial_closed : left.free = [] ∧ right.free = [] := by constructor <;> cbv

private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap
    (initial_good 0).native.machine.1 left right
    (SourceRecursiveIntersectionOriginalOutput.closed_original left heap (initial_good 0).native.machine.1.coherent
      originals.1 initial_closed.1)
    (SourceRecursiveIntersectionOriginalOutput.closed_original right heap (initial_good 0).native.machine.1.coherent
      originals.2 initial_closed.2)
    originals.1 originals.2 initial_closed.1 initial_closed.2

private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩

private theorem initial_fits (width : Nat) : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial_good width).native.machine.1⟩


open InternedNestedProvenance (Values)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
private def inputs : List (Value Symbol Guard) := [left,right,left,.reference .depth]
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0],[1],[2]]).getD ⟨.empty,[]⟩
private def paths := SourceEqualityClassTarget.operandPaths record.paths [0]
private theorem record_paths : record.paths = [[0],[1],[2]] := by cbv
private theorem selected : [0] ∈ record.paths := by rw [record_paths]; exact List.mem_cons_self
private theorem paths_eq : paths = [[1],[2]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0],[1],[2]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.terminal),(1,.terminal),(2,.terminal)],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem input_available (width : Nat) : Values (before width).native.machine.heap inputs := by
  intro value member
  simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact originals.1
  · exact originals.2
  · exact originals.1
  · exact InternedNestedProvenance.depth_available _
private theorem domains : ∀path∈paths,SourceEqualityProjectionPathDomain.ForestClosed path inputs := by
  intro path member
  rw [paths_eq] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · simpa [SourceEqualityProjectionPathDomain.ForestClosed,SourceEqualityProjectionPathDomain.NodeClosed,
      SourceEqualityProjectionGraph.select,inputs] using initial_closed.2
  · simpa [SourceEqualityProjectionPathDomain.ForestClosed,SourceEqualityProjectionPathDomain.NodeClosed,
      SourceEqualityProjectionGraph.select,inputs] using initial_closed.1
private theorem open_input : ¬MergedColdReaderClosedInputs.ClosedValues inputs := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [inputs])
  cases impossible
private def literal (width : Nat) := SourceCurrentAllocatedTargetWorker.target 8 16 64 16 128 inputs paths
  (before width) SourceCurrentMemoMergeGraph.empty
private def result (width : Nat) : Value Symbol Guard := match literal width with | .done value .. => value | _ => .empty
private def after (width : Nat) := (literal width).state
private def saved (width : Nat) := (literal width).memo
private theorem literal_done (width : Nat) : literal width = .done (result width) (after width) (saved width) := by
  have tag : (match literal width with | .done .. => true | _ => false) = true := by
    set_option cbv.maxSteps 200000000 in cbv
  cases found : literal width <;> simp_all only [result,after,saved,
    SourceCurrentAllocatedTargetWorker.Outcome.state,SourceCurrentAllocatedTargetWorker.Outcome.memo,Bool.false_eq_true]
private theorem empty_covered (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∀ambient,SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient
      (SourceCurrentMemoMergeGraph.empty : Memo) := by
  intro ambient key entry absent
  cases absent
private theorem power_large (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.add_assoc, Nat.pow_succ]
      omega

private theorem exists_room (p : SourceCurrentAllocatedNativeResourceForecast.Profile) :
    ∃ bits, SourceCurrentAllocatedNativeResourceForecast.Room bits p := by
  let total := p.nodes + p.edges + p.domains + 2 ^ (p.nodes + p.nodes * p.nodes)
  refine ⟨total + 1, ?_⟩
  have large := power_large total
  have one := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 1 by omega)
  have two := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 2 by omega)
  change p.nodes < 2 ^ (total + 1) ∧ p.edges ≤ 2 ^ (total + 1 + 2) ∧
    p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) < 2 ^ (total + 1 + 1)
  have nodes : p.nodes ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right p.nodes p.edges)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have edges : p.edges ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_left p.edges p.nodes)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have domains : p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) ≤ total :=
    Nat.add_le_add_right (Nat.le_add_left p.domains (p.nodes + p.edges)) _
  exact ⟨Nat.lt_of_le_of_lt nodes large,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt large) two),
    Nat.lt_of_le_of_lt domains (Nat.lt_of_lt_of_le large one)⟩

private theorem result_value (width : Nat) : result width = candidate := by
  set_option cbv.maxSteps 200000000 in cbv
private def installed (width : Nat) := SourceCurrentAllocatedSharedTargetState.store
  (SourceCurrentAllocatedSharedTargetState.initial (before width) (SourceCurrentMemoMergeGraph.empty : Memo))
  [0] (result width) (after width) (saved width)
private theorem installed_present (width : Nat) : (installed width).targets [0] = some (result width) := by
  simp [installed,SourceCurrentAllocatedSharedTargetState.store,put]

private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ bits next final,
    ∃ graph : SourceCurrentAllocatedTargetGraph.Target inputs paths (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty (result (bits + 2)) (after (bits + 2)) (saved (bits + 2)),
      built = .done root heap ∧ record.paths = [[0],[1],[2]] ∧ SourceEqualityClassOrder.Coherent record ∧
      [0] ∈ record.paths ∧ paths = [[1],[2]] ∧ ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
      SourceCurrentAllocatedTargetWorker.target 8 16 64 16 128 inputs paths (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty = .done (result (bits + 2)) (after (bits + 2)) (saved (bits + 2)) ∧
      result (bits + 2) = candidate ∧
      SourceCurrentAllocatedTargetComplete.TargetReads formulas solver graph EndpointMemoGateTrace.empty final ∧
      SourceCurrentAllocatedTargetComplete.Receipt formulas solver next inputs paths (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty (result (bits + 2)) (after (bits + 2)) (saved (bits + 2))
        EndpointMemoGateTrace.empty final ∧
      Frame formulas solver next (after (bits + 2)) ∧
      Fits (SourceCurrentConstrainedCapTargetForecast.targetProfile inputs.length paths profile) (after (bits + 2)) ∧
      SourceCurrentAllocatedSharedTargetState.SlotReceipt (bits + 2) formulas solver record inputs
        (after (bits + 2)).native.machine.heap (saved (bits + 2)) [0] (result (bits + 2)) ∧
      SourceCurrentAllocatedSharedTargetState.Ready formulas solver next record inputs heap (installed (bits + 2)) ∧
      (installed (bits + 2)).targets [0] = some (result (bits + 2)) ∧
      SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record inputs [0] (installed (bits + 2)) =
        .done (result (bits + 2)) (installed (bits + 2)) ∧
      Available (installed (bits + 2)).checked.native.machine.heap (result (bits + 2)) ∧
      (result (bits + 2)).free = []
 := by
  obtain ⟨bits,room⟩ := exists_room (SourceCurrentConstrainedCapTargetForecast.targetProfile inputs.length paths profile)
  have reserved : SourceCurrentConstrainedCapTargetForecast.TargetReserved bits inputs.length paths profile := by
    rw [paths_eq] at room ⊢
    exact SourceCurrentConstrainedCapTargetForecast.reserved_of_final_room bits inputs.length [1] [[2]] profile room
  have frame := Frame.initial formulas solver inventory machine operations (initial_ready (bits + 2)) initial_guards rfl
  obtain ⟨next,final,graph,reads,receipt,returned,fits⟩ :=
    SourceCurrentActualTargetSemanticReads.target formulas solver inventory inputs paths (before (bits + 2))
      SourceCurrentMemoMergeGraph.empty profile frame (initial_fits (bits + 2)) (input_available (bits + 2))
      domains (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) reserved (literal_done (bits + 2))
  have slot := SourceCurrentActualTargetSemanticReads.slot_receipt formulas solver inventory record inputs [0] selected
    (before (bits + 2)) SourceCurrentMemoMergeGraph.empty profile frame (initial_fits (bits + 2))
    (input_available (bits + 2)) domains (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
    EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) reserved (literal_done (bits + 2))
    (after (bits + 2)).native.machine.heap (saved (bits + 2))
    (SourceEqualityRequiredCache.pure_keeps _ returned.ready.semantic.ready) (extends_refl _)
  have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record inputs heap
    (before (bits + 2)) SourceCurrentMemoMergeGraph.empty frame.ready frame.admitted
    (SourceEqualityRequiredCache.pure_keeps _ frame.ready.semantic.ready)
    (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
  have sharedReady := initialReady.store [0] selected graph reads receipt
  have retrieved := sharedReady.receipts [0] (result (bits + 2)) (installed_present (bits + 2))
  have available := retrieved.available
  have hit := SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record inputs [0]
    (installed (bits + 2)) (result (bits + 2)) (installed_present (bits + 2))
  exact ⟨bits,next,final,graph,constructed,record_paths,coherent,selected,paths_eq,open_input,
    literal_done (bits + 2),result_value (bits + 2),reads,receipt,returned,fits,slot,sharedReady,
    installed_present (bits + 2),hit,available.1,available.2⟩

/-- Initial source data give exact semantic reads for an unequal-fuel target and its later warm slot. -/
theorem unequal_fuel_target_slot (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ bits next final,
    ∃ graph : SourceCurrentAllocatedTargetGraph.Target inputs paths (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty (result (bits + 2)) (after (bits + 2)) (saved (bits + 2)),
      built = .done root heap ∧ record.paths = [[0],[1],[2]] ∧ SourceEqualityClassOrder.Coherent record ∧
      [0] ∈ record.paths ∧ paths = [[1],[2]] ∧ ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
      SourceCurrentAllocatedTargetWorker.target 8 16 64 16 128 inputs paths (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty = .done (result (bits + 2)) (after (bits + 2)) (saved (bits + 2)) ∧
      result (bits + 2) = candidate ∧
      SourceCurrentAllocatedTargetComplete.TargetReads formulas solver graph EndpointMemoGateTrace.empty final ∧
      SourceCurrentAllocatedTargetComplete.Receipt formulas solver next inputs paths (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty (result (bits + 2)) (after (bits + 2)) (saved (bits + 2))
        EndpointMemoGateTrace.empty final ∧
      Frame formulas solver next (after (bits + 2)) ∧
      Fits (SourceCurrentConstrainedCapTargetForecast.targetProfile inputs.length paths profile) (after (bits + 2)) ∧
      SourceCurrentAllocatedSharedTargetState.SlotReceipt (bits + 2) formulas solver record inputs
        (after (bits + 2)).native.machine.heap (saved (bits + 2)) [0] (result (bits + 2)) ∧
      SourceCurrentAllocatedSharedTargetState.Ready formulas solver next record inputs heap (installed (bits + 2)) ∧
      (installed (bits + 2)).targets [0] = some (result (bits + 2)) ∧
      SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record inputs [0] (installed (bits + 2)) =
        .done (result (bits + 2)) (installed (bits + 2)) ∧
      Available (installed (bits + 2)).checked.native.machine.heap (result (bits + 2)) ∧
      (result (bits + 2)).free = []
 := witness formulas solver

end MicroCFTA.TargetSemanticKernels
