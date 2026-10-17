import MicroCFTA.SourceCurrentConstrainedCapCheckedJointClosed
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ActualCheckedMixedIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConstrainedCapKernelJoint (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial numeric resources construct a mixed Mu query and its exact full-state warm repeat. -/
theorem mixed_cold_then_warm (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap)
    (leftEntry bodyEntry muEntry : Interned NodeKey) (badEdge plainEdge : EdgeValue Symbol Guard)
    (leftLevel bodyLevel : Nat) (depthProbe ordinaryProbe : Value Symbol Guard)
    (badChildren : badEdge.children = []) (plainChildren : plainEdge.children = [])
    (bad : ¬ Plain badEdge.entry.key.constraint) (plain : Plain plainEdge.entry.key.constraint)
    (leftAvailable : Available machine.heap (.node leftEntry [badEdge] leftLevel []))
    (rightAvailable : Available machine.heap (.mu muEntry (.node bodyEntry [plainEdge] bodyLevel []) depthProbe ordinaryProbe))
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    let left := Value.node leftEntry [badEdge] leftLevel []
    let right := Value.mu muEntry (.node bodyEntry [plainEdge] bodyLevel []) depthProbe ordinaryProbe
    ∃ (inputModel : InputMeaning (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)))
      (inputRanked : RankedInput (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
      (fuel : Nat) (value : Value Symbol Guard) (after : Checked (bits + 2)),
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        ⟨initial (bits + 2) machine, operations⟩ value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
          (SourceEqualityPCSGuard.holds formulas solver) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) after = .done value after ∧
      Context Plain machine.heap after.native.machine ∧
      SourceCurrentConstrainedCapCheckedJointCache.Stored Plain machine.heap after.native ∧
      Cap Plain 1 value ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified
        (SourceCurrentConstrainedCapPairOccurrences.sourceWeight Plain machine.heap)
        (SourceCurrentConstrainedCapNonplainRank.pairRank Plain left right) value ∧
      value.free = [] ∧
      (∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term) ∧
      (∃ key handle,
        after.native.nodes.table key = some handle ∧
        after.native.nodes.cells handle = some ⟨⟨IntersectionEmptyDomain.emptyDomain, left, right⟩, .returned value⟩) ∧
      compileNode ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ = compileMu IntersectionEmptyDomain.emptyDomain left right ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated Plain left := by
  let left := Value.node leftEntry [badEdge] leftLevel []
  let right := Value.mu muEntry (.node bodyEntry [plainEdge] bodyLevel []) depthProbe ordinaryProbe
  let domain := IntersectionEmptyDomain.emptyDomain
  let request : NodeRequest Symbol Guard := ⟨domain, left, right⟩
  let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
  have leftCap : Cap Plain 1 left := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, badChildren, List.not_mem_nil] at member
  have bodyAnnotated : SourceEqualityAnnotationLanguage.Annotated Plain (.node bodyEntry [plainEdge] bodyLevel []) := by
    apply SourceEqualityAnnotationLanguage.Annotated.node
    · intro edge member
      have same := List.mem_singleton.mp member
      subst edge
      exact plain
    · intro child member
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, plainChildren, List.not_mem_nil] at member
  have rightCap : Cap Plain 1 right := .plain 1 (.mu muEntry _ depthProbe ordinaryProbe bodyAnnotated)
  have leftClosed : left.free = [] := rfl
  have rightClosed : right.free = [] := rfl
  have originalInputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs machine.heap good.native.machine.1 domain
    left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨inputModel, inputRanked, fuel, value, after, receipt, _scoped, _idle, closed, meaning,
      context, stored, _capped, _classified, _original, _fresh, _current⟩ :=
    SourceCurrentConstrainedCapCheckedJointClosed.cold_complete bits 1 formulas solver machine operations good semantic guards
      left right originalInputs.1 originalInputs.2.1 leftAvailable rightAvailable leftClosed rightClosed
      leftCap rightCap nodes edges room
  let key : Triple (bits + 2) := flatKey (bits + 2) domain (.node leftEntry.identity) (.mu muEntry.identity)
  have requested : SourceRecursiveIntersectionMemo.requestKey (bits + 2) request.domain request.left request.right = some key :=
    sourceKey_complete (bits + 2) domain left.referenceOf right.referenceOf (.node leftEntry.identity) (.mu muEntry.identity) rfl rfl
  have repeated := SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace fuel request before after value good.native key requested receipt.toReceipt.trace
  obtain ⟨handle, published, returned⟩ := repeated.1
  have warmLaw := stored.nodes handle request value returned
  have warmResult := warmLaw 1 (SourceCurrentConstrainedCapOriginalSupport.empty Plain machine.heap)
    originalInputs leftCap rightCap
  have branch : SourceRecursiveIntersectionControl.decision domain.key left right = .rightMu := by
    simp [domain, left, right, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
      SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf, SourceRecursiveIntersectionControl.greater,
      SourceRecursiveIntersectionControl.compareValue, SourceRecursiveIntersectionControl.tag,
      SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionControl.payload,
      Value.referenceOf, Value.free, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey]
    decide
  refine ⟨inputModel, inputRanked, fuel, value, after, receipt, repeated.2, context, stored, warmResult.1, warmResult.2.1, closed, meaning, ⟨key, handle, published, returned⟩, ?_, ?_⟩
  · change compileNode ⟨domain, left, right⟩ = compileMu domain left right
    simp only [compileNode, branch]
  · intro annotated
    exact bad (SourceCurrentHereditaryConstructors.node_edge annotated badEdge List.mem_cons_self).1

#print axioms mixed_cold_then_warm
#check @mixed_cold_then_warm
end MicroCFTA.ActualCheckedMixedIntegration
