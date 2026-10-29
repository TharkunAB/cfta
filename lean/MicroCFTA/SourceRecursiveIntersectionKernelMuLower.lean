import MicroCFTA.SourceRecursiveIntersectionKernelReturnDegree
import MicroCFTA.SourceRecursiveIntersectionKernelLowerSequencing

/-!
# All-outcome allocation bounds for an actual kernel Mu branch

The smaller-runtime hypothesis bounds the actual body heap.
The closed return theorem bounds its value when the body succeeds.
The optional binder bound includes probes and pending construction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open InternedStoredPlanBinderDepth InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionThunks (NodeRequest NodeReady)
open SourceRecursiveIntersectionCode (NodeScope NodeBelow mu_identities mu_request_below)
open SourceRecursiveIntersectionNative (nodeSemantic)
open SourceRecursiveIntersectionInputView (view)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionControl (pair)
open IntersectSchedule

/-- Every actual Mu outcome bounds each complete new body from the original request. -/
theorem mu_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state : Machine Symbol Guard),
      Valid state → NodeReady state request →
      Grows source state.heap → Extends source.nodes.issued state.heap.nodes.issued →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      Lower state.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
        (execute emptyGuard conjoin fuel request.domain request.left request.right state).state.heap)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (recursive : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (state : Machine Symbol Guard) (valid : Valid state) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap) :
    Lower state.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
      (mu (execute emptyGuard conjoin fuel) request.domain request.left request.right state).state.heap := by
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
  have bodyLower := nodeIH child childScope childComplete enteredState enteredValid childReady
    growth history semantic opened
  have initialLower : Lower state.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
      (execute emptyGuard conjoin fuel actual.1 (body request.left) (body request.right) enteredState).state.heap :=
    bodyLower.mono (Nat.add_le_add_left (Nat.le_of_lt smaller) limit)
  simp only [mu, firstIdentity, secondIdentity]
  apply result_bind_lower _ _ initialLower
  intro bodyValue bodyAfter bodyDone accumulated
  have checked := execute_checked emptyGuard conjoin fuel actual.1 (body request.left) (body request.right)
    enteredState enteredValid childReady.1 childReady.2.1 childReady.2.2
  have bodyAvailable := checked.result bodyValue bodyAfter bodyDone
  obtain ⟨bodySemantic, bodyOpened, bodyBound⟩ := node_result_degree source facts limit sourceBounded
    holds emptyGuard conjoin fuel child childScope childComplete enteredState bodyAfter enteredValid childReady
    growth history semantic opened bodyValue bodyDone
  have constructorLower := (SourceRecursiveIntersectionMaybeMu.lower (pair first second) bodyValue bodyAfter.heap
    bodySemantic.1 bodySemantic.2 bodyOpened bodyAvailable).mono
    (show valueDepth bodyValue + 1 ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete by omega)
  have lifted : Lower bodyAfter.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
      (construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue bodyAfter.heap) bodyAfter).state.heap := by
    cases built : SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue bodyAfter.heap <;>
      simpa only [built, construction, Result.state, InternedNestedConstruction.Outcome.state] using constructorLower
  exact accumulated.trans lifted

end MicroCFTA.SourceRecursiveIntersectionKernel
