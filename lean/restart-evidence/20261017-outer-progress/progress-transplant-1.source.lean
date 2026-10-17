import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentAllocatedPartialWorker

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.OuterProgressTransplant
open Cache InternedConstructorTemplates InternedProbeProvenance
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
private def b := ((children original)[0]?).getD .empty
private def tau := ((children original)[1]?).getD .empty
private def first := SourceEqualityConstraintAllocation.construct outer.equalities Cache.emptyState
private def second := SourceEqualityConstraintAllocation.construct inner.equalities first.2
private def third := SourceEqualityConstraintAllocation.construct plain.equalities second.2
private def outerValue : SourceEqualityConstraintAllocation.Value := match first.1 with | .ok value => value | _ => .contradiction
private def innerValue : SourceEqualityConstraintAllocation.Value := match second.1 with | .ok value => value | _ => .contradiction
private def plainValue : SourceEqualityConstraintAllocation.Value := match third.1 with | .ok value => value | _ => .contradiction
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 third.2 heap
private noncomputable def parent := SourceCurrentAllocatedParentWorker.edge 16 16 16 16 16 16 16 16 128 0
  ("roots", .top) outer plainValue [b,tau] before.checked before.fourth before.merge
private noncomputable def returned : EdgeValue Symbol Guard := match parent with
  | .done edge _ _ _ => edge
  | .failed .. => .mk ⟨⟨("roots", .top), [], plain⟩, 0⟩ []

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
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> simp) original heap built_done
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct _ initial.1.good.operations
  exact ⟨⟨⟨initial.1.good.native,initial.1.good.heap,allocated.1,initial.1.good.fields.grows allocated.2.1⟩,
    initial.1.semantic,initial.1.costs,initial.1.scopedCache,initial.1.idle⟩,initial.2⟩

/-- The original finite branch and recursive branch are accepted by the actual primary gate. -/
theorem primary_admitted : SourceCurrentAllocatedGateWorker.primary 16 [b,tau] [[0],[1,0]] before.checked =
    .done false before.checked := by cbv

/-- The actual parent copies the finite guard into the recursive branch at a deeper occurrence. -/
theorem parent_transplant :
    (match parent with
    | .done edge _ _ _ =>
      edge.children.length = 2 ∧
      (((children (edge.children[1]?.getD .empty))[0]?.getD .empty).referenceOf = b.referenceOf) ∧
      ((nodeEdges (edge.children[1]?.getD .empty)).map (fun row => row.entry.key.constraint) = [plain]) ∧
      (nodeEdges ((children (edge.children[1]?.getD .empty))[0]?.getD .empty)).map
        (fun row => row.entry.key.constraint) = [inner]
    | .failed .. => False) := by cbv

end MicroCFTA.OuterProgressTransplant
