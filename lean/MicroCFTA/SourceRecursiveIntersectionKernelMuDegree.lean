import MicroCFTA.SourceRecursiveIntersectionCompileMuBounds
import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.SourceRecursiveIntersectionMaybeMuDepth
import MicroCFTA.SourceRecursiveIntersectionOpenDepthEffects

/-!
# Degree of an actual completed kernel Mu branch

The smaller-runtime induction hypothesis handles the actual body call.
The entered child has a strictly smaller semantic required fuel.
The actual optional binder adds at most one to the returned body degree.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionThunks (NodeRequest NodeReady)
open SourceRecursiveIntersectionCode (NodeScope NodeBelow mu_identities mu_request_below)
open SourceRecursiveIntersectionNative (nodeSemantic)
open SourceRecursiveIntersectionInputView (view)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionControl (pair)
open IntersectSchedule

/-- The actual Mu branch retains both heaps and fits its original semantic request bound. -/
theorem mu_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (_sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard)
      (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state after : Machine Symbol Guard),
      Valid state → NodeReady state request →
      Grows source state.heap → Extends source.nodes.issued state.heap.nodes.issued →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      ∀ value, execute emptyGuard conjoin fuel request.domain request.left request.right state = .done value after →
        SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
          valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (recursive : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (state after : Machine Symbol Guard) (valid : Valid state) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap)
    (value : Value Symbol Guard)
    (done : mu (execute emptyGuard conjoin fuel) request.domain request.left request.right state = .done value after) :
    SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
      valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete := by
  obtain ⟨first, second, firstIdentity, secondIdentity⟩ := mu_identities request recursive
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains request.domain.key
    request.left request.right first second
  let enteredState : Machine Symbol Guard := {state with domains := actual.2}
  let child : NodeRequest Symbol Guard := ⟨actual.1, body request.left, body request.right⟩
  have below : NodeBelow source holds (requiredFuel (view source holds) (nodeSemantic request) complete) child :=
    mu_request_below source facts holds request scope complete recursive state.domains valid.2
      first second firstIdentity secondIdentity
  obtain ⟨childScope, childComplete, smaller⟩ := below
  obtain ⟨enteredValid, _enteredExtension, enteredDomain⟩ := entered state valid request.domain ready.1
    request.left request.right ready.2.1 ready.2.2 first second
  have childReady : NodeReady enteredState child :=
    ⟨enteredDomain, body_available state.heap request.left ready.2.1,
      body_available state.heap request.right ready.2.2⟩
  have checked := execute_checked emptyGuard conjoin fuel actual.1 (body request.left) (body request.right)
    enteredState enteredValid childReady.1 childReady.2.1 childReady.2.2
  simp only [mu, firstIdentity, secondIdentity] at done
  change (execute emptyGuard conjoin fuel actual.1 (body request.left) (body request.right) enteredState).bind
    (fun result reached => construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second)
      result reached.heap) reached) = .done value after at done
  cases bodyDone : execute emptyGuard conjoin fuel actual.1 (body request.left) (body request.right) enteredState with
  | failed failure reached =>
      simp only [bodyDone, Result.bind] at done
      cases done
  | done bodyValue bodyAfter =>
      have bodyAvailable := checked.result bodyValue bodyAfter bodyDone
      obtain ⟨bodySemantic, bodyOpened, bodyBound⟩ := nodeIH child childScope childComplete
        enteredState bodyAfter enteredValid childReady growth history semantic opened bodyValue bodyDone
      have constructed : construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second)
          bodyValue bodyAfter.heap) bodyAfter = .done value after := by
        simpa only [bodyDone, Result.bind] using done
      have semanticAfter := SourceRecursiveIntersectionSemanticHeap.optionalBinder (pair first second)
        bodyValue bodyAfter.heap bodySemantic bodyAvailable
      have openedAfter := SourceRecursiveIntersectionOpenDepthEffects.optionalBinder (pair first second)
        bodyValue bodyAfter.heap bodySemantic bodyOpened bodyAvailable
      cases built : SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue bodyAfter.heap with
      | pending key heap =>
          simp only [built, construction] at constructed
          cases constructed
      | done returned heap =>
          have literal : (Result.done returned {bodyAfter with heap := heap} : Result Symbol Guard (Value Symbol Guard)) =
              .done value after := by
            simpa only [built, construction] using constructed
          obtain ⟨valueSame, afterSame⟩ := Result.done.inj literal
          have returnedBound := SourceRecursiveIntersectionMaybeMu.result_le (pair first second)
            bodyValue bodyAfter.heap bodySemantic.1 bodySemantic.2 bodyOpened bodyAvailable returned heap built
          have valueBound : valueDepth value ≤ valueDepth bodyValue + 1 := by
            simpa only [valueSame] using returnedBound
          refine ⟨?_, ?_, ?_⟩
          · rw [← afterSame]
            change SemanticHeap heap
            simpa only [built, InternedNestedConstruction.Outcome.state] using semanticAfter
          · rw [← afterSame]
            change InternedOpenDepthReadback.Heap heap
            simpa only [built, InternedNestedConstruction.Outcome.state] using openedAfter
          · omega

end MicroCFTA.SourceRecursiveIntersectionKernel
