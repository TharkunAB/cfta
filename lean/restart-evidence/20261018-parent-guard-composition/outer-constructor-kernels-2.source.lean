import MicroCFTA.SourceCurrentOuterConstructorBounds
import MicroCFTA.SourceCurrentConjunctionGuardUniverse
import MicroCFTA.SourceEqualityPCSNativeEdge
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

namespace MicroCFTA.OuterConstructorKernels
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq FullSyntax.Formula := fun first second =>
  decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private instance : DecidableEq Node := by classical exact inferInstance
private def top : Guard := SourceEqualityConstraintConstructors.top
private def expression : Syntax Symbol Guard := .node [.mk ("parent",.top) top [
  .binder false (.node [.mk ("left",.top) top []]),
  .binder false (.node [.mk ("right",.top) top []])]]
private def constructed := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match constructed with | .done value _ => value | _ => .empty
private def heap := constructed.state
private def fallback : EdgeValue Symbol Guard := (run (makeEdge ("fallback",.top) top []) empty).1
private def original := (nodeEdges root)[0]?.getD fallback
private def first := original.children[0]?.getD (Value.empty : Node)
private def second := original.children[1]?.getD (Value.empty : Node)
private def neutralBuild := SourceEqualityConstraintAllocation.intern (some []) Cache.emptyState
private def neutral := neutralBuild.1
private def checked : SourceEqualityNativeDemand.State 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial neutralBuild.2⟩
private def caller := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def called := SourceCurrentAllocatedPartialWorker.children 2 0 0 0 0 0 0 0 0 0 0 neutral original.children caller
private def results : List Node := match called with | .done values _ => values | _ => []
private def middle := called.state
private def rebuilt := SourceCurrentAllocatedRawRebuild.edge original results middle.checked
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next,heap.edges.next,0,InternedValueMassHeap.initialBound heap⟩
private def alphabet := SourceCurrentConjunctionGuardUniverse.guards heap
private theorem constructed_done : constructed = .done root heap := by cbv
private theorem facts : InternedNestedFacts.Facts heap :=
  (SourceEqualityRequiredSemanticCache.constructed expression root heap constructed_done).ready.semantic.1.normal.facts
private theorem source_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed_done
private theorem first_available : Available heap first :=
  source_available.children first (by cbv; exact List.mem_cons_self)
private theorem second_available : Available heap second :=
  source_available.children second (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem original_resident : EdgeResident heap original :=
  InternedEdgeResidency.resident_edges heap facts.linked root source_available.resident original
    (by cbv; exact List.mem_cons_self)
private theorem called_done : called = .done results middle := by
  have tag : (match called with | .done .. => true | _ => false) = true := by cbv
  cases observed : called <;> simp_all only [results,middle,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]
private theorem results_eq : results = [cleanup first,cleanup second] := by cbv
private theorem heap_same : middle.checked.native.machine.heap = heap := by cbv
private theorem domain_same : middle.checked.native.machine.domains.next = 0 := by cbv
private theorem input_fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile middle.checked := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [heap_same,profile,Nat.le_refl]
  · simp only [heap_same,profile,Nat.le_refl]
  · simp only [domain_same,profile,Nat.le_refl]
  · simpa only [heap_same,profile] using InternedValueMassHeap.initial heap facts
private theorem input_known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) middle.checked.native.machine.heap := by
  rw [heap_same]
  exact SourceCurrentConjunctionGuardUniverse.initial heap facts
private theorem input_resident : EdgeResident middle.checked.native.machine.heap original := by
  rw [heap_same]; exact original_resident
private theorem input_available : Values middle.checked.native.machine.heap results := by
  rw [heap_same,results_eq]
  intro value member
  rcases List.mem_cons.mp member with rfl | later
  · exact InternedConstructionProvenance.cleanup_available first first_available
  · rcases List.mem_cons.mp later with rfl | impossible
    · exact InternedConstructionProvenance.cleanup_available second second_available
    · cases impossible
private theorem witness :
    constructed = .done root heap ∧
    (∃ identity body depth ordinary,first = .mu identity body depth ordinary) ∧
    (∃ identity body depth ordinary,second = .mu identity body depth ordinary) ∧
    called = .done results middle ∧ results = [cleanup first,cleanup second] ∧
    middle.checked.native.machine.heap = heap ∧
    rebuilt.1.entry.key.symbol = original.entry.key.symbol ∧ rebuilt.1.entry.key.constraint = original.entry.key.constraint ∧
    rebuilt.1.children = results ∧ rebuilt.2.native.machine.heap.edges.next = heap.edges.next + 1 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits (SourceCurrentOuterConstructorBounds.profile profile) rebuilt.2 ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) rebuilt.2.native.machine.heap := by
  have bounded := SourceCurrentOuterConstructorBounds.children_rebuild alphabet profile original called_done
    input_fits input_known input_resident input_available
  refine ⟨constructed_done,?_,?_,called_done,results_eq,heap_same,?_,?_,?_,?_,bounded.1,bounded.2.1⟩
  · have tag : (match first with | .mu .. => true | _ => false) = true := by cbv
    cases observed : first <;> simp_all only [Bool.false_eq_true]
    exact ⟨_,_,_,_,rfl⟩
  · have tag : (match second with | .mu .. => true | _ => false) = true := by cbv
    cases observed : second <;> simp_all only [Bool.false_eq_true]
    exact ⟨_,_,_,_,rfl⟩
  · cbv
  · cbv
  · cbv
  · cbv

/-- Actual Mu cleanup feeds a new raw edge with derived numeric and finite guard bounds. -/
theorem cleanup_then_raw_edge :
    constructed = .done root heap ∧
    (∃ identity body depth ordinary,first = .mu identity body depth ordinary) ∧
    (∃ identity body depth ordinary,second = .mu identity body depth ordinary) ∧
    called = .done results middle ∧ results = [cleanup first,cleanup second] ∧
    middle.checked.native.machine.heap = heap ∧
    rebuilt.1.entry.key.symbol = original.entry.key.symbol ∧ rebuilt.1.entry.key.constraint = original.entry.key.constraint ∧
    rebuilt.1.children = results ∧ rebuilt.2.native.machine.heap.edges.next = heap.edges.next + 1 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits (SourceCurrentOuterConstructorBounds.profile profile) rebuilt.2 ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) rebuilt.2.native.machine.heap := witness
end
end MicroCFTA.OuterConstructorKernels
