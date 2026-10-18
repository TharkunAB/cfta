import MicroCFTA.SourceCurrentClassFoldStructuralOrigins
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
# A selected positive continuation can come from the competing slot

The actual class worker returns a positive row and a positive child.
That child occurs in the competing input and not in the selected original.
The original-slot positional Below relation therefore does not hold.
The actual inherited prefix also drops the cross-child equality on descent.
This example establishes no infinite execution or implementation defect.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.ClassFoldStructuralKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionThunks
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
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) top []]
private def inner (guard : Guard) : Syntax Symbol Guard := .node [.mk ("inner",.top) guard [leaf,leaf,leaf]]
private def wrapper (guard : Guard) : Syntax Symbol Guard := .node [.mk ("wrapper",.top) top [inner guard]]
private def expression : Syntax Symbol Guard := .node [.mk ("forest",.top) top [wrapper guardA,wrapper guardB]]
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
private def records := [record,record]
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
    simp only [expression,wrapper,inner,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,or_self] at member ⊢
    tauto
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
private noncomputable def bits := Classical.choose exists_width
private theorem width_large : 8 ≤ bits := (Classical.choose_spec exists_width).1
private theorem width_room : SourceCurrentAllocatedNativeResourceForecast.Room bits ceiling :=
  (Classical.choose_spec exists_width).2
private def remainder (n : Nat) := n % (2^(bits+2))
private theorem small_mod (n : Nat) : n % (2^(bits+2)) = if n < 1024 then n else remainder n := by
  split
  · apply Nat.mod_eq_of_lt
    have bound : 1024 ≤ 2^(bits+2) := by
      exact Nat.pow_le_pow_right (by decide) (by have := width_large; omega)
    omega
  · rfl
attribute [local cbv_eval] small_mod
private theorem symbolic_word : (BitVec.ofNat (bits+2) 5).toNat = 5 := by cbv
end MicroCFTA.ClassFoldStructuralKernels
