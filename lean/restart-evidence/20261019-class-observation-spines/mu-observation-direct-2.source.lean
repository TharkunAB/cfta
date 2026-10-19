import MicroCFTA.SourceCurrentClassFoldStructuralOrigins
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.MergedFreshOrdinaryGraphOrigins
import MicroCFTA.SourceEqualityRequiredExecution
import MicroCFTA.SourceCurrentClassSelectedChildLineage
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentActualClassSemanticReads
import MicroCFTA.SourceCurrentParentInitialRoom
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentActualClassDispatch
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.SourceCurrentAllocatedInheritedPrefix
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# An actual native Mu result exposes a positive row

Two source-built used Mu operands have distinct positive body guards.
The original primary gate returns true. Required retains both Mu roots.
The literal class edit returns a Mu. A later row read unfolds it.
The observed row has the combined full guard. No productivity is claimed.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.MuObservationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def top : Guard := ⟨some [],.top⟩
private def guardA : Guard := ⟨some [[[0],[1]]],.top⟩
private def guardB : Guard := ⟨some [[[0],[2]]],.top⟩
private def guardAB : Guard := ⟨some [[[0],[1],[2]]],.top⟩
private def recursive (guard : Guard) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("inner",.top) guard [.var 0,.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("forest",.top) top [recursive guardA,recursive guardB]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def inputs := children root
private def first := inputs[0]?.getD .empty
private def second := inputs[1]?.getD .empty
private def one := SourceEqualityConstraintAllocation.construct guardA.equalities Cache.emptyState
private def oneValue : EqValue := match one.1 with | .ok value => value | .error _ => .contradiction
private def two := SourceEqualityConstraintAllocation.construct guardB.equalities one.2
private def twoValue : EqValue := match two.1 with | .ok value => value | .error _ => .contradiction
private def allocation := SourceEqualityConstraintAllocation.construct top.equalities two.2
private def inherited : EqValue := match allocation.1 with | .ok value => value | .error _ => .contradiction
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityConstraintMemoAllocation.initial allocation.2
private def before (width : Nat) : Checked width := ⟨initial width machine,operations⟩
private def record := (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private def records := [record]
private theorem built_done : built = .done root heap := by cbv
private theorem input_shape : inputs = [first,second] := by cbv
private theorem cachedA : SourceEqualityGuardReadback.Cached guardA.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem cachedB : SourceEqualityGuardReadback.Cached guardB.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[2]]] = .normalized [[[0],[2]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem ready (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) := by
  have oneHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState one.2 [guardA] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cachedA (show one = (.ok oneValue,one.2) by cbv)
  have twoHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState two.2 [guardA,guardB] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      oneHistory cachedB (show two = (.ok twoValue,two.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [guardA,guardB,top] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      twoHistory SourceEqualityGuardReadback.empty_cached (show allocation = (.ok inherited,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [guardA,guardB,top] := by
    intro guard member
    simp only [expression,recursive,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false] at member ⊢
    simpa only [or_assoc,or_left_comm,or_comm,or_self] using member
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid
    expression covered root heap built_done).1
private theorem available : InternedNestedProvenance.Values heap inputs :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done).children
private theorem closed : first.free = [] ∧ second.free = [] := by constructor <;> cbv
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (ready 0).good.native.machine.1 first second
    (SourceRecursiveIntersectionOriginalOutput.closed_original first heap (ready 0).good.native.machine.1.coherent
      (available first (by rw [input_shape]; simp)) closed.1)
    (SourceRecursiveIntersectionOriginalOutput.closed_original second heap (ready 0).good.native.machine.1.coherent
      (available second (by rw [input_shape]; simp)) closed.2)
    (available first (by rw [input_shape]; simp)) (available second (by rw [input_shape]; simp)) closed.1 closed.2
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next,heap.edges.next,machine.domains.next,InternedValueMassHeap.initialBound heap⟩
private noncomputable def ceiling := SourceCurrentConstrainedCapClassForecast.foldProfile records inputs.length profile
private theorem exists_width : ∃ bits, 8 ≤ bits ∧ SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling := by
  let chosen := SourceCurrentParentInitialRoom.roomBits ceiling
  have room := SourceCurrentParentInitialRoom.room_computed ceiling
  refine ⟨chosen+8,by omega,?_⟩
  have pow0 : 2^chosen ≤ 2^(chosen+8) := Nat.pow_le_pow_right (by decide) (by omega)
  have pow1 : 2^(chosen+1) ≤ 2^(chosen+8+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have pow2 : 2^(chosen+2) ≤ 2^(chosen+8+2) := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨Nat.lt_of_lt_of_le room.1 pow0,Nat.le_trans room.2.1 pow2,Nat.lt_of_lt_of_le room.2.2 pow1⟩
private noncomputable opaque widthData : {n : Nat // 8 ≤ n ∧ SourceCurrentAllocatedNativeResourceForecast.Room n ceiling} :=
  ⟨Classical.choose exists_width,Classical.choose_spec exists_width⟩
private noncomputable def bits := widthData.val
private theorem width_large : 8 ≤ bits := widthData.property.1
private theorem width_room : SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling := widthData.property.2
private theorem wide : 1024 ≤ 2^(bits+2) := by
  change 2^10 ≤ 2^(bits+2)
  exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) (by have := width_large; omega)
private noncomputable def concreteWord (n : Nat) : BitVec (bits+2) :=
  if h : n < 1024 then BitVec.ofNatLT n (Nat.lt_of_lt_of_le h wide) else BitVec.ofNat (bits+2) n
private theorem word_small (n : Nat) : BitVec.ofNat (bits+2) n = concreteWord n := by
  unfold concreteWord
  split
  · apply BitVec.eq_of_toNat_eq
    change n % 2^(bits+2) = n
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by assumption) wide)
  · rfl
attribute [local cbv_eval] word_small
private theorem symbolic_word : (BitVec.ofNat (bits+2) 5).toNat = 5 := by cbv
private noncomputable def classed := SourceCurrentAllocatedClassWorker.runClass 4 8 8 64 16 256
  record inputs (before (bits+2)) SourceCurrentMemoMergeGraph.empty
private noncomputable def outputs := match classed with | .done values .. => values | .failed .. => []
private noncomputable def result := outputs[0]?.getD .empty
private def fallback := (run (makeEdge ("missing",.top) top []) heap).1
private noncomputable def after := classed.state.native.machine.heap
private noncomputable def projected := SourceEqualityProjectionWorker.forest 2 0 [0] outputs after
private noncomputable def unfoldCall := InternedFreshOrdinaryStoredSubstitution.unfold result after
private noncomputable def exposed : Node := match unfoldCall with | .done value _ => value | _ => .empty
private noncomputable def unfoldedHeap := unfoldCall.state
private noncomputable def readCall := MergedFreshOrdinaryExposure.nodeEdges 4 result after
private noncomputable def observed := match readCall with | .done rows _ => rows | _ => []
private noncomputable def reader := readCall.state
private noncomputable def row := observed[0]?.getD fallback
private theorem class_done : classed = .done outputs classed.state classed.memo := by
  have tag : (match classed with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : classed with
  | done values state memo => simp only [outputs,actual,SourceCurrentAllocatedClassWorker.Outcome.state,
      SourceCurrentAllocatedClassWorker.Outcome.memo]
  | failed fault state => rw [actual] at tag; cases tag
private theorem original_gate : SourceCurrentAllocatedGateWorker.primary 8 inputs record.paths (before (bits+2)) =
    .done true (before (bits+2)) := by cbv
private theorem required_identity : SourceEqualityRequiredExecution.requireAll 4 0
    (record.paths.map (List.map Int.ofNat)) inputs heap = .done inputs heap := by cbv
private theorem selected : outputs[0]? = some result := by cbv
private theorem mu_result : (match result with
  | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true
  | _ => False) := by cbv
private theorem projected_done : projected = .done result after := by cbv
private theorem unfolded_done : unfoldCall = .done exposed unfoldedHeap := by cbv
private theorem read_done : readCall = .done observed reader := by cbv
private theorem observed_facts : observed[0]? = some row ∧ row.entry.key.constraint = guardAB ∧
    row.entry.key.symbol = ("inner",.top) ∧ row.children = [result,result,result] ∧ nodeEdges result = [] := by
  exact ⟨by cbv,by cbv,by cbv,by cbv,by cbv⟩
end MicroCFTA.MuObservationKernels
