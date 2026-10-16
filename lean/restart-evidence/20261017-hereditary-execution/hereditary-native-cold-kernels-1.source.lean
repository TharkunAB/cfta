import MicroCFTA.SourceCurrentHereditaryNativeCold
import MicroCFTA.SourceCurrentHereditaryExposure
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.HereditaryNativeColdKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryConstruction
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A cold query on two actual Mu operands produces the causal store for a later actual head. -/
theorem recursive_query_then_head (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady machine.heap)
    (leftEntry rightEntry : Interned InternedBinderProtocol.NodeKey)
    (leftBody leftDepth leftOrdinary rightBody rightDepth rightOrdinary : Value Symbol Guard)
    (leftOriginal : Original (.mu leftEntry leftBody leftDepth leftOrdinary))
    (rightOriginal : Original (.mu rightEntry rightBody rightDepth rightOrdinary))
    (leftAvailable : Available machine.heap (.mu leftEntry leftBody leftDepth leftOrdinary))
    (rightAvailable : Available machine.heap (.mu rightEntry rightBody rightDepth rightOrdinary))
    (leftClosed : (Value.mu leftEntry leftBody leftDepth leftOrdinary).free = [])
    (rightClosed : (Value.mu rightEntry rightBody rightDepth rightOrdinary).free = [])
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1))
    (stored : MuStored Plain machine.heap)
    (leftAnnotated : Annotated Plain (.mu leftEntry leftBody leftDepth leftOrdinary))
    (rightAnnotated : Annotated Plain (.mu rightEntry rightBody rightDepth rightOrdinary)) :
    ∃ fuel value after head final,
      SourceEqualityNativeDemand.execute (fuel + 1)
        (.code (requestNode IntersectionEmptyDomain.emptyDomain
          (.mu leftEntry leftBody leftDepth leftOrdinary) (.mu rightEntry rightBody rightDepth rightOrdinary)))
        ⟨initial (bits + 2) machine, operations⟩ = .done value after ∧
      SourceEqualityRequiredHead.Head value after.native.machine.heap head final ∧
      SourceCurrentHereditaryNativeControl.Stored Plain machine.heap after ∧
      MuStored Plain final ∧ Annotated Plain value ∧ Annotated Plain head ∧
      SourceMemoGate.unconstrained head = true := by
  obtain ⟨_model, _ranked, fuel, value, after, receipt, _scope, _idle, closed, _meaning, retained, annotated, _unconstrained⟩ :=
    SourceCurrentHereditaryNativeCold.cold_complete bits formulas solver machine operations good semantic
      (.mu leftEntry leftBody leftDepth leftOrdinary) (.mu rightEntry rightBody rightDepth rightOrdinary)
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed nodes edges room stored leftAnnotated rightAnnotated
  obtain ⟨head, final, actual, _keeps, _available, _closed, _ordinary⟩ := SourceEqualityRequiredHead.complete value after.native.machine.heap
    receipt.keeps.ready receipt.result closed
  have headReturned := SourceCurrentHereditaryExposure.head Plain actual receipt.keeps.ready receipt.result closed annotated retained.constructors
  exact ⟨fuel, value, after, head, final, receipt.done, actual, retained, headReturned.1, annotated, headReturned.2,
    SourceCurrentHereditaryUnconstrained.unconstrained head headReturned.2⟩

/-- Original raw self syntax derives both causal stores before its own finite native query. -/
theorem constructed_self_query (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (nodes : (InternedFreshOrdinaryConstruction.build
      (.binder false (.var 0) : InternedNestedConstruction.Syntax Symbol Guard) [] InternedConstructorTemplates.empty).state.nodes.next < 2 ^ bits)
    (edges : (InternedFreshOrdinaryConstruction.build
      (.binder false (.var 0) : InternedNestedConstruction.Syntax Symbol Guard) [] InternedConstructorTemplates.empty).state.edges.next ≤ 2 ^ (bits + 2))
    (room : 2 ^ ((InternedFreshOrdinaryConstruction.build
      (.binder false (.var 0) : InternedNestedConstruction.Syntax Symbol Guard) [] InternedConstructorTemplates.empty).state.nodes.next +
      (InternedFreshOrdinaryConstruction.build
        (.binder false (.var 0) : InternedNestedConstruction.Syntax Symbol Guard) [] InternedConstructorTemplates.empty).state.nodes.next *
      (InternedFreshOrdinaryConstruction.build
        (.binder false (.var 0) : InternedNestedConstruction.Syntax Symbol Guard) [] InternedConstructorTemplates.empty).state.nodes.next) < 2 ^ (bits + 1)) :
    ∃ original heap fuel value after,
      InternedFreshOrdinaryConstruction.build (.binder false (.var 0)) [] InternedConstructorTemplates.empty = .done original heap ∧
      SourceEqualityNativeDemand.execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain original original))
        ⟨initial (bits + 2) ⟨heap, Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.empty⟩ = .done value after ∧
      SourceCurrentHereditaryNativeControl.Stored Plain heap after ∧ Annotated Plain value ∧
      SourceMemoGate.unconstrained value = true ∧ value.free = [] := by
  let expression : InternedNestedConstruction.Syntax Symbol Guard := .binder false (.var 0)
  obtain ⟨original, heap, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed Plain expression
    (by simp [expression, SourceEqualityAnnotationConstruction.Allowed])
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression original heap built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result original heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression original heap built
  have originalInput := SourceRecursiveIntersectionOriginalOutput.closed_original original heap
    semantic.ready.semantic.1.normal.facts.coherent available closed
  have noEdges : SourceEqualityAnnotationHeap.Heap (fun _ : Guard => False) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun _ : Guard => False) expression
      (by simp [expression, SourceEqualityAnnotationConstruction.Allowed]) [] InternedConstructorTemplates.empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, InternedNestedConstruction.Outcome.state] using checked
  let machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
  have good : SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨initial (bits + 2) machine, SourceEqualityConstraintMemoAllocation.empty⟩ : Checked (bits + 2)) :=
    ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
        ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩,
      semantic.ready, SourceEqualityConstraintMemoAllocation.initial_valid Cache.emptyState Cache.empty_valid,
      fun key edge found => (noEdges key edge found).elim⟩
  have nodeSupply : machine.heap.nodes.next < 2 ^ bits := by
    simpa only [← built, InternedNestedConstruction.Outcome.state] using nodes
  have edgeSupply : machine.heap.edges.next ≤ 2 ^ (bits + 2) := by
    simpa only [← built, InternedNestedConstruction.Outcome.state] using edges
  have domainSupply : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) < 2 ^ (bits + 1) := by
    simpa only [built, InternedNestedConstruction.Outcome.state, machine, Cache.emptyState, Nat.zero_add] using room
  obtain ⟨_model, _ranked, fuel, value, after, receipt, _scope, _idle, resultClosed, _meaning, resultStored, resultAnnotated, unconstrained⟩ :=
    SourceCurrentHereditaryNativeCold.cold_complete bits formulas solver machine SourceEqualityConstraintMemoAllocation.empty good semantic
      original original originalInput originalInput available available closed closed nodeSupply edgeSupply domainSupply stored annotated annotated
  exact ⟨original, heap, fuel, value, after, built, receipt.done, resultStored, resultAnnotated, unconstrained, resultClosed⟩

end MicroCFTA.HereditaryNativeColdKernels

#print axioms MicroCFTA.HereditaryNativeColdKernels.recursive_query_then_head
#check @MicroCFTA.HereditaryNativeColdKernels.recursive_query_then_head

#print axioms MicroCFTA.HereditaryNativeColdKernels.constructed_self_query
#check @MicroCFTA.HereditaryNativeColdKernels.constructed_self_query
