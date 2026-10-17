import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.MergedOrdinaryHeight
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Actual parent height growth through an accepted unequal-length class

A source-built productive plain Mu is paired with a finite constrained node.
The actual primary gate admits their unequal-length class. The literal
allocated parent copies the finite value into a deeper ordinary child.
It retains the original raw guard and raises the returned edge height from
2 to 3. The new child has the same ordinary height as the original parent.
This refutes strict ordinary-height descent on this transition. It does
not assert an outer cycle, divergence, or a Haskell behavior defect.
-/
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.OuterParentWarmWitness
open Cache InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionKernel InternedEdgeResidency
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

private def plain : Guard := ⟨some [], .top⟩
private def inner : Guard := ⟨some [[[0], [1]]], .top⟩
private def outer : Guard := ⟨some [[[0], [1, 0]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf", .top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair", .top) inner [leaf, leaf]]
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf", .top) plain [], .mk ("pair", .top) plain [.var 0, .var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) outer [finite, recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def b := ((children original)[0]?).getD (Value.empty : Value Symbol Guard)
private def tau := ((children original)[1]?).getD (Value.empty : Value Symbol Guard)
private def first := SourceEqualityConstraintAllocation.construct outer.equalities Cache.emptyState
private def second := SourceEqualityConstraintAllocation.construct inner.equalities first.2
private def third := SourceEqualityConstraintAllocation.construct plain.equalities second.2
private def outerValue : SourceEqualityConstraintAllocation.Value := match first.1 with | .ok value => value | _ => .contradiction
private def innerValue : SourceEqualityConstraintAllocation.Value := match second.1 with | .ok value => value | _ => .contradiction
private def plainValue : SourceEqualityConstraintAllocation.Value := match third.1 with | .ok value => value | _ => .contradiction
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 third.2 heap
private noncomputable def parent := SourceCurrentAllocatedParentWorker.edge 16 16 16 16 16 16 16 16 128 0
  ("roots", .top) outer plainValue [b,tau] before.checked before.fourth before.merge
private def sourceEdge : EdgeValue Symbol Guard :=
  ((nodeEdges original)[0]?).getD (run (makeEdge ("roots", .top) outer [b,tau]) heap).1

private theorem cached_inner : SourceEqualityGuardReadback.Cached inner.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem cached_outer : SourceEqualityGuardReadback.Cached outer.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0], [1, 0]]] = .normalized [[[0], [1, 0]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState third.2 [outer,inner,plain] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState first.2 [outer] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached_outer (show first = (.ok outerValue,first.2) by cbv)
  have two : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [outer,inner] :=
    SourceEqualityOriginalAllocationHistory.History.construct one cached_inner (show second = (.ok innerValue,second.2) by cbv)
  exact SourceEqualityOriginalAllocationHistory.History.construct two SourceEqualityGuardReadback.empty_cached
    (show third = (.ok plainValue,third.2) by cbv)
private theorem built_done : built = .done original heap := by cbv
private theorem source_ready : SourceCurrentConjunctionClassScan.Ready before.checked ∧
    Available heap original ∧ original.free = [] ∧ SourceRecursiveIntersectionInputView.Original original := by
  have initial := SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid expression
    (fun guard member => by
      simp only [expression,finite,leaf,recursive,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,false_or] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) original heap built_done
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct _ initial.1.good.operations
  exact ⟨⟨⟨initial.1.good.native,initial.1.good.heap,allocated.1,initial.1.good.fields.grows allocated.2.1⟩,
    initial.1.semantic,initial.1.costs,initial.1.scopedCache,initial.1.idle⟩,initial.2⟩

/-- The original finite branch and recursive branch are accepted by the actual primary gate. -/
private theorem primary_admitted : SourceCurrentAllocatedGateWorker.primary 16 [b,tau] [[0],[1,0]] before.checked =
    .done false before.checked := by cbv

/-- The actual parent copies the finite guard into the recursive branch at a deeper occurrence. -/
private theorem parent_transplant :
    (match parent with
    | .done edge _ _ _ =>
      edge.entry.key.constraint = outer ∧ edge.children.length = 2 ∧
      MergedOrdinaryHeight.edgeHeight sourceEdge = 2 ∧ MergedOrdinaryHeight.edgeHeight edge = 3 ∧
      MergedOrdinaryHeight.height original = 3 ∧
      MergedOrdinaryHeight.height ((edge.children[1]?).getD (Value.empty : Value Symbol Guard)) = 3 ∧
      (edge.children[0]?).getD (Value.empty : Value Symbol Guard) = b ∧
      ((((children ((edge.children[1]?).getD (Value.empty : Value Symbol Guard)))[0]?).getD (Value.empty : Value Symbol Guard)).referenceOf = b.referenceOf) ∧
      ((nodeEdges ((edge.children[1]?).getD (Value.empty : Value Symbol Guard))).map (fun row => row.entry.key.constraint) = [plain]) ∧
      (nodeEdges (((children ((edge.children[1]?).getD (Value.empty : Value Symbol Guard)))[0]?).getD (Value.empty : Value Symbol Guard))).map
        (fun row => row.entry.key.constraint) = [inner]
    | .failed .. => False) := by cbv

private noncomputable def result : EdgeValue Symbol Guard := match parent with
  | .done edge _ _ _ => edge
  | .failed .. => sourceEdge
private theorem parent_done : parent = .done result parent.state parent.fourth parent.memo := by
  cases same : parent with
  | done edge after fourth memo => simp only [result,same,SourceCurrentAllocatedParentWorker.Outcome.state,
      SourceCurrentAllocatedParentWorker.Outcome.fourth,SourceCurrentAllocatedParentWorker.Outcome.memo]
  | failed fault after fourth memo =>
      have impossible := parent_transplant
      rw [same] at impossible
      exact False.elim impossible

private noncomputable def outerCall := SourceCurrentAllocatedPartialWorker.nodeCall
  24 16 16 16 16 16 16 16 16 128 0 ⟨plainValue,original⟩ before

/-- The actual finite outer call returns and leaves the copied finite value ready in its original cell. -/
theorem finite_outer_warm :
    (match outerCall with
    | .done value after =>
      MergedOrdinaryHeight.height value = 4 ∧
      (SourceCurrentAllocatedPartialState.beginNode ⟨plainValue,b⟩ after).2.1 = .ready b ∧
      (SourceCurrentAllocatedPartialState.beginNode ⟨plainValue,b⟩ after).2.2 = after
    | .failed .. => False) := by cbv
#check @finite_outer_warm
#print axioms finite_outer_warm
end MicroCFTA.OuterParentWarmWitness
