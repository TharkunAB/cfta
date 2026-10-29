import MicroCFTA.SourceRecursiveIntersectionNativeWalkLower
import MicroCFTA.SourceRecursiveIntersectionNativeReturnDegreeFacts

namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedBinderProtocol
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual union prefixes retain the original parent bound through completed children. -/
theorem union_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (bound : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard), NodeBelow source holds bound request →
      ∀ (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → NodeReady current.machine request →
      Grows source current.machine.heap → Extends source.nodes.issued current.machine.heap.nodes.issued →
      SemanticHeap current.machine.heap → InternedOpenDepthReadback.Heap current.machine.heap →
      WordRanges emptyGuard conjoin (.node request .pure) current →
      ∀ fuel, Lower current.machine.heap (limit + bound)
        (execute emptyGuard conjoin fuel (.node request .pure) current).state.machine.heap)
    (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (known : SourceRecursiveIntersectionKernel.Domain state.machine domain)
    (available : Available state.machine.heap other)
    (membersAvailable : ∀ member ∈ members, Available state.machine.heap member)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (memberBounds : ∀ member ∈ members,
      if left then NodeBelow source holds bound ⟨domain, member, other⟩
      else NodeBelow source holds bound ⟨domain, other, member⟩)
    (ranges : WordRanges emptyGuard conjoin
      ((walk (fun member => if left then requestNode domain member other else requestNode domain other member) members).bind
        fun values => .work (makeUnion values) .pure) state) (fuel : Nat) :
    Lower state.machine.heap (limit + bound)
      (execute emptyGuard conjoin fuel
        ((walk (fun member => if left then requestNode domain member other else requestNode domain other member) members).bind
          fun values => .work (makeUnion values) .pure) state).state.machine.heap := by
  let request (member : Value Symbol Guard) : NodeRequest Symbol Guard :=
    if left then ⟨domain, member, other⟩ else ⟨domain, other, member⟩
  let call (member : Value Symbol Guard) : Code Symbol Guard (Value Symbol Guard) := .node (request member) .pure
  have callSame : call = (fun member => if left then requestNode domain member other else requestNode domain other member) := by
    funext member
    cases left <;> rfl
  have bounds : ∀ member ∈ members, NodeBelow source holds bound (request member) := by
    intro member present
    cases left <;> exact memberBounds member present
  let invariant (current : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current ∧
    SourceRecursiveIntersectionKernel.Domain current.machine domain ∧ Available current.machine.heap other ∧
    (∀ member ∈ members, Available current.machine.heap member) ∧
    Grows source current.machine.heap ∧ Extends source.nodes.issued current.machine.heap.nodes.issued ∧
    SemanticHeap current.machine.heap ∧ InternedOpenDepthReadback.Heap current.machine.heap
  have ready (member : Value Symbol Guard) (present : member ∈ members)
      (current : SourceRecursiveIntersectionThunks.State width Symbol Guard) (known : invariant current) :
      NodeReady current.machine (request member) := by
    cases left
    · exact ⟨known.2.1, known.2.2.1, known.2.2.2.1 member present⟩
    · exact ⟨known.2.1, known.2.2.2.1 member present, known.2.2.1⟩
  have limited : ∀ member ∈ members, ∀ current, invariant current →
      WordRanges emptyGuard conjoin (call member) current →
      ∀ inner, Lower current.machine.heap (limit + bound)
        (execute emptyGuard conjoin inner (call member) current).state.machine.heap := by
    intro member present current currentKnown callRanges inner
    have inputs := ready member present current currentKnown
    obtain ⟨currentValid, _domain, _other, _members, currentGrowth, currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    exact nodeIH (request member) (bounds member present) current currentValid inputs
      currentGrowth currentHistory currentSemantic currentOpened callRanges inner
  have preserved : ∀ member ∈ members, ∀ current, invariant current →
      WordRanges emptyGuard conjoin (call member) current →
      ∀ inner value after, execute emptyGuard conjoin inner (call member) current = .done value after → invariant after := by
    intro member present current currentKnown callRanges inner value after completed
    have inputs := ready member present current currentKnown
    obtain ⟨currentValid, currentDomain, currentOther, currentMembers, currentGrowth,
      currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    obtain ⟨scope, complete, _below⟩ := bounds member present
    obtain ⟨afterValid, extension, _valueAvailable, afterSemantic, afterOpened, _degree⟩ :=
      node_return_degree_facts source facts limit sourceBounded holds width emptyGuard conjoin inner
        (request member) scope complete current after currentValid inputs currentGrowth currentHistory
        currentSemantic currentOpened callRanges value completed
    exact ⟨afterValid, currentDomain.grows domain extension, extension.available other currentOther,
      (fun member included => extension.available member (currentMembers member included)),
      grows_trans currentGrowth extension.heap, extends_trans currentHistory extension.history, afterSemantic, afterOpened⟩
  rw [← callSame] at ranges ⊢
  have walkRanges := ranges.before_bind emptyGuard conjoin (walk call members)
    (fun values => .work (makeUnion values) .pure) state
  apply execute_bind_lower emptyGuard conjoin fuel (walk call members)
    (fun values => .work (makeUnion values) .pure) state (limit + bound)
  · exact walk_prefix_lower emptyGuard conjoin call invariant (limit + bound) members limited preserved state
      ⟨valid, known, available, membersAvailable, growth, history, semantic, opened⟩ walkRanges
  · intro _ values after _ outer
    exact work_lower emptyGuard conjoin outer (makeUnion values) after (limit + bound)
      (InternedShallowHeap.makeUnion_noNewMu values after.machine.heap)

end MicroCFTA.SourceRecursiveIntersectionNative
