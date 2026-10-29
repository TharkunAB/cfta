import MicroCFTA.SourceRecursiveIntersectionKernelReturnDegree
import MicroCFTA.SourceRecursiveIntersectionKernelLowerSequencing

namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- All union outcomes retain exact old Mu records or the parent body bound. -/
theorem union_lower {Symbol Guard : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source) (limit : Nat)
    (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state : Machine Symbol Guard) (_valid : Valid state) (_ready : NodeReady state request)
      (_growth : Grows source state.heap)
      (_history : Extends source.nodes.issued state.heap.nodes.issued)
      (_semantic : SemanticHeap state.heap) (_opened : InternedOpenDepthReadback.Heap state.heap),
      Lower state.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
        (execute emptyGuard conjoin fuel request.domain request.left request.right state).state.heap)
    (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (bound : Nat)
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (available : Available state.heap other)
    (membersAvailable : ∀ member ∈ members, Available state.heap member)
    (growth : Grows source state.heap)
    (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap)
    (memberBounds : ∀ member ∈ members,
      if left then NodeBelow source holds bound ⟨domain, member, other⟩
      else NodeBelow source holds bound ⟨domain, other, member⟩) :
    Lower state.heap (limit + bound)
      (((walk (fun member =>
        if left then execute emptyGuard conjoin fuel domain member other
        else execute emptyGuard conjoin fuel domain other member) members state).bind
        fun values middle => work (makeUnion values) middle).state.heap) := by
  let request (member : Value Symbol Guard) : NodeRequest Symbol Guard :=
    if left then ⟨domain, member, other⟩ else ⟨domain, other, member⟩
  let call (member : Value Symbol Guard) (current : Machine Symbol Guard) :=
    execute emptyGuard conjoin fuel (request member).domain (request member).left (request member).right current
  have callSame : call = (fun member =>
      if left then execute emptyGuard conjoin fuel domain member other
      else execute emptyGuard conjoin fuel domain other member) := by
    funext member current
    cases left <;> rfl
  have bounds : ∀ member ∈ members, NodeBelow source holds bound (request member) := by
    intro member present
    cases left <;> exact memberBounds member present
  let invariant (current : Machine Symbol Guard) : Prop :=
    Valid current ∧ Domain current domain ∧ Available current.heap other ∧
      (∀ member ∈ members, Available current.heap member) ∧
      Grows source current.heap ∧ Extends source.nodes.issued current.heap.nodes.issued ∧
      SemanticHeap current.heap ∧ InternedOpenDepthReadback.Heap current.heap
  have ready (member : Value Symbol Guard) (present : member ∈ members)
      (current : Machine Symbol Guard) (known : invariant current) : NodeReady current (request member) := by
    cases left
    · exact ⟨known.2.1, known.2.2.1, known.2.2.2.1 member present⟩
    · exact ⟨known.2.1, known.2.2.2.1 member present, known.2.2.1⟩
  have limited : ∀ member ∈ members, ∀ current, invariant current →
      Lower current.heap (limit + bound) (call member current).state.heap := by
    intro member present current currentKnown
    obtain ⟨scope, complete, below⟩ := bounds member present
    have inputs := ready member present current currentKnown
    obtain ⟨currentValid, _currentDomain, _currentOther, _currentMembers,
      currentGrowth, currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    exact (nodeIH (request member) scope complete current currentValid
      inputs currentGrowth currentHistory currentSemantic currentOpened).mono
      (Nat.add_le_add_left (Nat.le_of_lt below) limit)
  have preserved : ∀ member ∈ members, ∀ current value after, invariant current →
      call member current = .done value after → invariant after := by
    intro member present current value after currentKnown completed
    have inputs := ready member present current currentKnown
    obtain ⟨currentValid, currentDomain, currentOther, currentMembers,
      currentGrowth, currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    obtain ⟨scope, complete, _below⟩ := bounds member present
    have actual : execute emptyGuard conjoin fuel
        (request member).domain (request member).left (request member).right current = .done value after := completed
    have checked := execute_checked emptyGuard conjoin fuel
      (request member).domain (request member).left (request member).right current
      currentValid inputs.1 inputs.2.1 inputs.2.2
    have afterValid : Valid after := by
      simpa only [actual, Result.state] using checked.valid
    have extension : Extension current after := by
      simpa only [actual, Result.state] using checked.extension
    have retained := node_result_degree source facts limit sourceBounded holds emptyGuard conjoin fuel
      (request member) scope complete current after currentValid inputs currentGrowth currentHistory
      currentSemantic currentOpened value actual
    exact ⟨afterValid, currentDomain.grows domain extension, extension.available other currentOther,
      (fun member included => extension.available member (currentMembers member included)),
      grows_trans currentGrowth extension.heap, extends_trans currentHistory extension.history,
      retained.1, retained.2.1⟩
  have walked := walk_lower call invariant (limit + bound) members limited preserved state
    ⟨valid, known, available, membersAvailable, growth, history, semantic, opened⟩
  have finished := result_bind_lower (walk call members state)
    (fun values middle => work (makeUnion values) middle) walked (by
      intro values middle _completed lower
      change Lower state.heap (limit + bound) (run (makeUnion values) middle.heap).2
      exact preserve middle.heap _ lower (InternedShallowHeap.makeUnion_noNewMu values middle.heap))
  simpa only [callSame] using finished

end MicroCFTA.SourceRecursiveIntersectionKernel
