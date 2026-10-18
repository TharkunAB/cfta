import MicroCFTA.SourceCurrentOuterRebuildGuardAlphabet
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentConjunctionGuardUniverse
import MicroCFTA.SourceEqualityPCSNativeEdge
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

namespace MicroCFTA.OuterRebuildKernels
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
private theorem checked_same : middle.checked = checked := by cbv
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready checked := by
  have allocation : SourceEqualityConstraintAllocation.construct top.equalities Cache.emptyState =
      (.ok neutral, neutralBuild.2) := by cbv
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState neutralBuild.2 [top] := by
    simpa only [List.nil_append, top] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityConstraintConstructors.top_cached allocation
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid expression
    (fun guard member => by
      have same : guard = top := by simpa [expression,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards] using member
      subst guard
      exact List.mem_cons_self) root heap constructed_done).1
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedPartialInitialization.inventory expression root heap constructed_done
private theorem initial_frame (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory middle.checked := by
  rw [checked_same]
  exact SourceCurrentConstrainedCapGeneratedQueryResources.Frame.initial formulas solver inventory
    ⟨heap,Cache.emptyState⟩ (SourceEqualityConstraintMemoAllocation.initial neutralBuild.2) initial_ready
    (SourceCurrentConstrainedCapGuardExecution.closed_heap _ expression) rfl
private def rootIdentity : Interned InternedBinderProtocol.NodeKey := match root with
  | .node identity _ _ _ => identity
  | _ => ⟨0,.node []⟩
private def rootDepth := root.depth
private def rootFree := root.free
private theorem root_shape : root = .node rootIdentity [original] rootDepth rootFree := by cbv
private def rebuiltNode := SourceCurrentAllocatedRawRebuild.modify root [original] [rebuilt.1] rebuilt.2
private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    constructed = .done root heap ∧
    called = .done [cleanup first,cleanup second] middle ∧
    rebuilt.2.native.machine.heap.edges.next = heap.edges.next + 1 ∧
    rebuiltNode.2.native.machine.heap.nodes.next = rebuilt.2.native.machine.heap.nodes.next + 1 ∧
    SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory original results middle.checked rebuilt.1 rebuilt.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory rebuilt.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits (SourceCurrentOuterConstructorBounds.profile profile) rebuilt.2 ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) rebuilt.2.native.machine.heap ∧
    SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory root [original] [rebuilt.1] rebuilt.2
      rebuiltNode.1 rebuiltNode.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory rebuiltNode.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits
      (SourceCurrentOuterConstructorBounds.profile (SourceCurrentOuterConstructorBounds.profile profile)) rebuiltNode.2 ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) rebuiltNode.2.native.machine.heap := by
  have edge := SourceCurrentOuterRebuildGuardAlphabet.edge alphabet formulas solver inventory profile original results
    middle.checked (initial_frame formulas solver) input_fits input_known input_resident input_available
    (SourceCurrentOuterConstructorBounds.children_length called_done)
  have source : Available rebuilt.2.native.machine.heap root := edge.1.effects.keeps.available root (by
    change Available middle.checked.native.machine.heap root
    rw [heap_same]
    exact source_available)
  have rows : InternedNestedProvenance.Edges rebuilt.2.native.machine.heap [rebuilt.1] := by
    intro row member
    have same := List.mem_singleton.mp member
    subst row
    exact edge.1.resident
  have node := SourceCurrentOuterRebuildGuardAlphabet.modify alphabet formulas solver inventory
    (SourceCurrentOuterConstructorBounds.profile profile) rootIdentity [original] [rebuilt.1] rootDepth rootFree
    rebuilt.2 edge.2.1 edge.2.2.1 edge.2.2.2 (by simpa only [← root_shape] using source) rows rfl
  rw [← root_shape] at node
  refine ⟨constructed_done,?_,?_,?_,edge.1,edge.2.1,edge.2.2.1,edge.2.2.2,node⟩
  · simpa only [results_eq] using called_done
  · cbv
  · cbv

/-- Source-built Mu cleanup feeds both exact raw allocation endpoints. -/
theorem cleanup_edge_node (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    constructed = .done root heap ∧
    called = .done [cleanup first,cleanup second] middle ∧
    rebuilt.2.native.machine.heap.edges.next = heap.edges.next + 1 ∧
    rebuiltNode.2.native.machine.heap.nodes.next = rebuilt.2.native.machine.heap.nodes.next + 1 ∧
    SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory original results middle.checked rebuilt.1 rebuilt.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory rebuilt.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits (SourceCurrentOuterConstructorBounds.profile profile) rebuilt.2 ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) rebuilt.2.native.machine.heap ∧
    SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory root [original] [rebuilt.1] rebuilt.2
      rebuiltNode.1 rebuiltNode.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory rebuiltNode.2 ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits
      (SourceCurrentOuterConstructorBounds.profile (SourceCurrentOuterConstructorBounds.profile profile)) rebuiltNode.2 ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) rebuiltNode.2.native.machine.heap := witness formulas solver
end
end MicroCFTA.OuterRebuildKernels
