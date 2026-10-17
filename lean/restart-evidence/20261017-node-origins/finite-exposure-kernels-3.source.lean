import MicroCFTA.SourceCurrentRequiredFiniteExposure

set_option linter.all true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.RequiredFiniteExposureKernels
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
open SourceCurrentRequiredUnionNormal SourceCurrentRequiredRowOrigins
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def plain : Guard := ⟨some [], .top⟩
private def constrained : Guard := ⟨some [[[0],[1]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("a", .top) plain []]
private def finite : Syntax Symbol Guard := .union [
  .node [.mk ("pair", .top) constrained [leaf,leaf]],
  .node [.mk ("other", .top) constrained [leaf,leaf]]]
private def finiteBuilt := InternedFreshOrdinaryConstruction.build finite [] empty
private def finiteValue : Value Symbol Guard := match finiteBuilt with | .done value _ => value | .pending .. => .empty
private def finiteHeap := finiteBuilt.state
private theorem finite_done : finiteBuilt = .done finiteValue finiteHeap := by cbv

/-- A source union of constrained finite nodes normalizes and supports every initial requirement. -/
theorem constrained_source_every_needed :
    ∃ (expression : Syntax Symbol Guard) (value : Value Symbol Guard) (heap : Heap),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      SourceEqualityRequiredSemanticCache.SemanticReady heap ∧ UnionNormal heap ∧ Available heap value ∧
      value.depth = 0 ∧ value.free = [] ∧ SourceMemoGate.unconstrained value = false ∧
      ∀ needed : SourceEqualityNeeded.Needed, ExposureSafe needed value := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed finite finiteValue finiteHeap finite_done
  have normal : UnionNormal finiteHeap := SourceCurrentRequiredUnionNormal.source finite
  have available := (InternedFreshOrdinaryFacts.closed_verified finite).result finiteValue finiteHeap finite_done
  have zero : finiteValue.depth = 0 := by cbv
  have closed : finiteValue.free = [] := by cbv
  refine ⟨finite,finiteValue,finiteHeap,finite_done,semantic,normal,available,zero,closed,?_,?_⟩
  · cbv
  · intro needed
    exact SourceCurrentRequiredFiniteExposure.finite_exposure needed finiteHeap semantic normal finiteValue available zero closed

private def nested : Syntax Symbol Guard := .binder false (.union [leaf, .var 0])
private def nestedBuilt := InternedFreshOrdinaryConstruction.build nested [] empty
private def nestedValue : Value Symbol Guard := match nestedBuilt with | .done value _ => value | .pending .. => .empty
private def nestedHeap := nestedBuilt.state
private def depthProbe : Value Symbol Guard := match nestedValue with | .mu _ _ depth _ => depth | _ => .empty
private def ordinaryProbe : Value Symbol Guard := match nestedValue with | .mu _ _ _ ordinary => ordinary | _ => .empty
private theorem nested_done : nestedBuilt = .done nestedValue nestedHeap := by cbv

/-- A raw source binder retains union records and reads its warm winner without calling a blocked callback. -/
theorem binder_warm_and_unfold :
    ∃ (expression : Syntax Symbol Guard) (value depth ordinary : Value Symbol Guard) (heap : Heap),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      UnionNormal heap ∧ 0 < value.depth ∧
      InternedNestedConstruction.request false depth ordinary
        (fun _ current => .pending (muKey depth ordinary) current) heap = .done value heap ∧
      UnionNormal (InternedFreshOrdinaryStoredSubstitution.unfold value heap).state ∧
      ∃ key entry members level free,
        heap.nodeRecords key = some (.union entry members level free) ∧ ordinaryEdges members = none := by
  refine ⟨nested,nestedValue,depthProbe,ordinaryProbe,nestedHeap,nested_done,?_,?_,?_,?_,?_⟩
  · exact SourceCurrentRequiredUnionNormal.source nested
  · cbv
  · cbv
  · exact SourceCurrentRequiredUnionNormal.unfold nestedValue nestedHeap (SourceCurrentRequiredUnionNormal.source nested)
  · let key := InternedBinderProtocol.NodeKey.union [.node 0, .ref .depth]
    let entry : Cache.Interned InternedBinderProtocol.NodeKey := ⟨1,key⟩
    let member : Value Symbol Guard := match InternedFreshOrdinaryConstruction.build leaf [] empty with
      | .done value _ => value
      | .pending .. => .empty
    refine ⟨key,entry,[member,.reference .depth],0,[.depth],?_,?_⟩ <;>
      dsimp only [entry,member,key] <;> cbv

private def pendingKey := muKey (Value.empty : Value Symbol Guard) .empty
private def reserved : Heap := {InternedConstructorTemplates.empty with nodes := (Cache.intern Cache.emptyState pendingKey).2}

/-- An actual reserved pending Mu read retains the invariant without any successful callback premise. -/
theorem reserved_pending :
    UnionNormal reserved ∧
    InternedNestedConstruction.request false .empty .empty
      (fun _ current => .done .empty current) reserved = .pending pendingKey reserved ∧
    UnionNormal (InternedNestedConstruction.request false .empty .empty
      (fun _ current => .done .empty current) reserved).state := by
  have initial : UnionNormal reserved := SourceCurrentRequiredUnionNormal.empty
  refine ⟨initial,?_,?_⟩
  · cbv
  · exact SourceCurrentRequiredUnionNormal.request false .empty .empty _ reserved initial
      (fun _ _ current => current)

end MicroCFTA.RequiredFiniteExposureKernels

#check @MicroCFTA.RequiredFiniteExposureKernels.constrained_source_every_needed
#print axioms MicroCFTA.RequiredFiniteExposureKernels.constrained_source_every_needed
#check @MicroCFTA.RequiredFiniteExposureKernels.binder_warm_and_unfold
#print axioms MicroCFTA.RequiredFiniteExposureKernels.binder_warm_and_unfold
#check @MicroCFTA.RequiredFiniteExposureKernels.reserved_pending
#print axioms MicroCFTA.RequiredFiniteExposureKernels.reserved_pending
