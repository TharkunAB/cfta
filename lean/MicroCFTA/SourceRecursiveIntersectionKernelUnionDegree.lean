import MicroCFTA.SourceRecursiveIntersectionCodeBounds
import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.SourceRecursiveIntersectionOpenDepthEffects
import MicroCFTA.InternedStoredPlanBinderDepthNormalization
import MicroCFTA.InternedMuDepthInventory

namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Ordered union requests pass actual returned heaps to the remaining requests. -/
theorem union_degree {Symbol Guard : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (_facts : InternedNestedFacts.Facts source) (limit : Nat)
    (_bounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state after : Machine Symbol Guard) (_valid : Valid state) (_ready : NodeReady state request)
      (_growth : Grows source state.heap)
      (_history : Extends source.nodes.issued state.heap.nodes.issued)
      (_semantic : SemanticHeap state.heap) (_opened : InternedOpenDepthReadback.Heap state.heap)
      (value : Value Symbol Guard)
      (_done : execute emptyGuard conjoin fuel request.domain request.left request.right state = .done value after),
      SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
        valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete)
    (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (parentRank : Nat)
    (state after : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (available : Available state.heap other)
    (membersAvailable : ∀ member ∈ members, Available state.heap member)
    (growth : Grows source state.heap)
    (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap)
    (memberBounds : ∀ member ∈ members,
      if left then NodeBelow source holds parentRank ⟨domain, member, other⟩
      else NodeBelow source holds parentRank ⟨domain, other, member⟩)
    (value : Value Symbol Guard)
    (done : ((walk (fun member =>
      if left then execute emptyGuard conjoin fuel domain member other
      else execute emptyGuard conjoin fuel domain other member) members state).bind
      fun values middle => work (makeUnion values) middle) = .done value after) :
    SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
      valueDepth value ≤ limit + parentRank := by
  let request (member : Value Symbol Guard) : NodeRequest Symbol Guard :=
    if left then ⟨domain, member, other⟩ else ⟨domain, other, member⟩
  let call (member : Value Symbol Guard) (current : Machine Symbol Guard) :=
    execute emptyGuard conjoin fuel (request member).domain (request member).left (request member).right current
  have callSame : call = (fun member =>
      if left then execute emptyGuard conjoin fuel domain member other
      else execute emptyGuard conjoin fuel domain other member) := by
    funext member current
    cases left <;> rfl
  have bounds : ∀ member ∈ members, NodeBelow source holds parentRank (request member) := by
    intro member present
    cases left <;> exact memberBounds member present
  have visit : ∀ (requests : List (Value Symbol Guard)) (current final : Machine Symbol Guard)
      (results : List (Value Symbol Guard)), WalkTrace call requests current results final →
      (∀ member ∈ requests, NodeBelow source holds parentRank (request member)) →
      Valid current → Domain current domain → Available current.heap other →
      (∀ member ∈ requests, Available current.heap member) →
      Grows source current.heap → Extends source.nodes.issued current.heap.nodes.issued →
      SemanticHeap current.heap → InternedOpenDepthReadback.Heap current.heap →
      Valid final ∧ Extension current final ∧ SemanticHeap final.heap ∧
        InternedOpenDepthReadback.Heap final.heap ∧
        ∀ result ∈ results, Available final.heap result ∧ valueDepth result ≤ limit + parentRank := by
    intro requests current final results trace
    induction trace with
    | nil current =>
        intro _ currentValid _ _ _ _ _ currentSemantic currentOpened
        exact ⟨currentValid, .refl current, currentSemantic, currentOpened,
          by intro result present; cases present⟩
    | cons member rest current result middle results final returned _restTrace ih =>
        intro currentBounds currentValid currentKnown currentAvailable currentMembers
          currentGrowth currentHistory currentSemantic currentOpened
        obtain ⟨scope, complete, below⟩ := currentBounds member List.mem_cons_self
        have ready : NodeReady current (request member) := by
          cases left
          · exact ⟨currentKnown, currentAvailable, currentMembers member List.mem_cons_self⟩
          · exact ⟨currentKnown, currentMembers member List.mem_cons_self, currentAvailable⟩
        have completed : execute emptyGuard conjoin fuel
            (request member).domain (request member).left (request member).right current = .done result middle := returned
        have checked := execute_checked emptyGuard conjoin fuel
          (request member).domain (request member).left (request member).right current
          currentValid ready.1 ready.2.1 ready.2.2
        have middleValid : Valid middle := by
          simpa only [completed, Result.state] using checked.valid
        have extension : Extension current middle := by
          simpa only [completed, Result.state] using checked.extension
        have returnedAvailable := checked.result result middle completed
        have advanced := nodeIH (request member) scope complete current middle currentValid ready
          currentGrowth currentHistory currentSemantic currentOpened result completed
        obtain ⟨finalValid, finalExtension, finalSemantic, finalOpened, finalResults⟩ :=
          ih (fun next present => currentBounds next (List.mem_cons_of_mem _ present)) middleValid
            (currentKnown.grows domain extension) (extension.available other currentAvailable)
            (fun next present => extension.available next (currentMembers next (List.mem_cons_of_mem _ present)))
            (grows_trans currentGrowth extension.heap) (extends_trans currentHistory extension.history)
            advanced.1 advanced.2.1
        refine ⟨finalValid, extension.trans finalExtension, finalSemantic, finalOpened, ?_⟩
        intro output present
        rcases List.mem_cons.mp present with rfl | present
        · exact ⟨finalExtension.available _ returnedAvailable,
            Nat.le_trans advanced.2.2 (Nat.add_le_add_left (Nat.le_of_lt below) limit)⟩
        · exact finalResults output present
  have observed : ((walk call members state).bind
      fun values middle => work (makeUnion values) middle) = .done value after := by
    simpa only [callSame] using done
  cases walked : walk call members state with
  | failed failure middle =>
      simp only [walked, Result.bind] at observed
      cases observed
  | done values middle =>
      obtain ⟨middleValid, _middleExtension, middleSemantic, middleOpened, outputs⟩ :=
        visit members state middle values ((walk_done_iff call members state values middle).mp walked)
          bounds valid known available membersAvailable growth history semantic opened
      have constructed : work (makeUnion values) middle = .done value after := by
        simpa only [walked, Result.bind] using observed
      obtain ⟨sameValue, sameState⟩ := work_done (makeUnion values) middle value after constructed
      rw [sameValue, sameState]
      exact ⟨SourceRecursiveIntersectionSemanticHeap.union values middle.heap middleSemantic
          (fun output present => (outputs output present).1),
        SourceRecursiveIntersectionOpenDepthEffects.union values middle.heap middleOpened,
        makeUnion_le values middle.heap middleValid.1.coherent middleValid.1.cached middleValid.1.linked
          (fun output present => (outputs output present).1) (limit + parentRank)
          (fun output present => (outputs output present).2)⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
