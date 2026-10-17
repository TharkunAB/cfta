import MicroCFTA.SourceCurrentGeneratedQueryGuardResources
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
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

namespace MicroCFTA.GuardTraceCheck
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

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .union [
    .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]]),
    .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0],
      .mk ("extra", .top) annotation [.var 0, .var 0]])]
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
      List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using member) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩


private def left : Value Symbol Guard := (children value)[0]?.getD .empty
private def right : Value Symbol Guard := (children value)[1]?.getD .empty
private theorem left_member : left ∈ children value := by
  cbv
  exact .head _
private theorem right_member : right ∈ children value := by
  cbv
  exact .tail _ (.head _)
private theorem left_available : Available heap left := (initial 0).2.1.children left left_member
private theorem right_available : Available heap right := (initial 0).2.1.children right right_member
private theorem left_closed : left.free = [] := by cbv
private theorem right_closed : right.free = [] := by cbv
private theorem distinct : left ≠ right := by
  have ids : left.referenceOf ≠ right.referenceOf := by cbv; decide
  intro same
  exact ids (congrArg Value.referenceOf same)
private theorem mu_inputs :
    (match left with | .mu .. => True | _ => False) ∧
    (match right with | .mu .. => True | _ => False) := by cbv
private def alphabet : List Guard := [annotation]
private theorem carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) heap := by
  have allowed : SourceEqualityAnnotationConstruction.Allowed (fun guard => guard ∈ alphabet) expression := by
    simp only [expression, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]
    repeat' first | exact List.mem_cons_self | constructor
  simpa only [heap, built] using SourceEqualityAnnotationConstruction.build
    (fun guard => guard ∈ alphabet) expression allowed [] empty (SourceEqualityAnnotationHeap.empty_heap _)
private theorem no_cap (depth : Nat) : ¬Cap depth left := by
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


private theorem initial_frame (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before width) :=
  Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl

/-- Two distinct constrained recursive operands construct their own finite query and initial guard forecast. -/
theorem constructed_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    left ≠ right ∧ (∀ depth, ¬Cap depth left) ∧
    (match left with | .mu .. => True | _ => False) ∧
    (match right with | .mu .. => True | _ => False) ∧
    ∃ bits next fuel result after,
      SourceCurrentGeneratedQueryFrameResources.Receipt profile formulas solver next fuel left right
        (before (bits + 2)) result after EndpointMemoGateTrace.empty ∧
      SourceEqualityAnnotationHeap.Heap
        (fun guard => guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile) after.native.machine.heap := by
  obtain ⟨bits, room⟩ := exists_room profile
  obtain ⟨next, fuel, result, after, receipt, known⟩ := SourceCurrentGeneratedQueryGuardResources.complete
    alphabet profile formulas solver inventory (before (bits + 2)) (initial_frame _ formulas solver)
    (initial_fits _) room left right left_available right_available left_closed right_closed
    carrier EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
  exact ⟨distinct, no_cap, mu_inputs.1, mu_inputs.2, bits, next, fuel, result, after, receipt, known⟩

/-- The produced Frame, numeric forecast, and carrier supply a second complete query in the populated state. -/
theorem constructed_query_chain
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ bits next fuel result middle finalInventory finalFuel finalResult after,
      SourceCurrentGeneratedQueryFrameResources.Receipt profile formulas solver next fuel left right
        (before (bits + 2)) result middle EndpointMemoGateTrace.empty ∧
      SourceCurrentGeneratedQueryFrameResources.Receipt
        (SourceCurrentAllocatedNativeResourceForecast.step profile) formulas solver finalInventory finalFuel left right
        middle finalResult after EndpointMemoGateTrace.empty ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈
        SourceCurrentGeneratedQueryGuardResources.forecast
          (SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
          (SourceCurrentAllocatedNativeResourceForecast.step profile)) after.native.machine.heap := by
  obtain ⟨bits, finalRoom⟩ := exists_room (SourceCurrentAllocatedNativeResourceForecast.step profile)
  have room := SourceCurrentAllocatedNativeResourceForecast.Room.mono finalRoom
    (SourceCurrentAllocatedNativeResourceForecast.step_ge profile)
  obtain ⟨next, fuel, result, middle, first, known⟩ := SourceCurrentGeneratedQueryGuardResources.complete
    alphabet profile formulas solver inventory (before (bits + 2)) (initial_frame _ formulas solver)
    (initial_fits _) room left right left_available right_available left_closed right_closed
    carrier EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
  obtain ⟨finalInventory, finalFuel, finalResult, after, second, finalKnown⟩ :=
    SourceCurrentGeneratedQueryGuardResources.complete
      (SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
      (SourceCurrentAllocatedNativeResourceForecast.step profile) formulas solver next middle first.frame
      first.fits finalRoom left right (first.query.effects.keeps.available left left_available)
      (first.query.effects.keeps.available right right_available) left_closed right_closed
      known EndpointMemoGateTrace.empty first.query.globals
  exact ⟨bits, next, fuel, result, middle, finalInventory, finalFuel, finalResult, after, first, second, finalKnown⟩

end MicroCFTA.GuardTraceCheck
#check @MicroCFTA.GuardTraceCheck.constructed_query
#print axioms MicroCFTA.GuardTraceCheck.constructed_query
#check @MicroCFTA.GuardTraceCheck.constructed_query_chain
#print axioms MicroCFTA.GuardTraceCheck.constructed_query_chain
