import MicroCFTA.SourceRecursiveIntersectionCompileMuBounds
import MicroCFTA.SourceRecursiveIntersectionNativeReturnDegreeFacts
import MicroCFTA.SourceRecursiveIntersectionNativeBindLower
import MicroCFTA.SourceRecursiveIntersectionNativePrimitiveLower

/-!
# Allocation bounds at every compiled Mu prefix

The actual entered child retains its original scope and smaller semantic rank.
Its completed return derives the optional-binder site's body bound.
Stopped children and pending constructors retain their exact reached heaps.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionInputView IntersectSchedule
open InternedStoredPlanBinderDepth InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every compiled Mu prefix derives its allocation bound from the original owner and child. -/
theorem compiled_mu_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (bounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (recursive : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (nodeIH : ∀ (child : NodeRequest Symbol Guard) (_scope : NodeScope source child)
      (childComplete : Completes (view source holds) (nodeSemantic child)),
      requiredFuel (view source holds) (nodeSemantic child) childComplete <
        requiredFuel (view source holds) (nodeSemantic request) complete →
      ∀ (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → NodeReady current.machine child →
      Grows source current.machine.heap → Extends source.nodes.issued current.machine.heap.nodes.issued →
      SemanticHeap current.machine.heap → InternedOpenDepthReadback.Heap current.machine.heap →
      WordRanges emptyGuard conjoin (.node child .pure) current → ∀ fuel,
      Lower current.machine.heap (limit + requiredFuel (view source holds) (nodeSemantic child) childComplete)
        (execute emptyGuard conjoin fuel (.node child .pure) current).state.machine.heap)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine request)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (compileMu request.domain request.left request.right) state)
    (fuel : Nat) :
    Lower state.machine.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
      (execute emptyGuard conjoin fuel (compileMu request.domain request.left request.right) state).state.machine.heap := by
  obtain ⟨first, second, firstIdentity, secondIdentity⟩ := mu_identities request recursive
  let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains request.domain.key
    request.left request.right first second
  let machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard := {state.machine with domains := actual.2}
  let current := advance state machine
  let child : NodeRequest Symbol Guard :=
    ⟨actual.1, SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩
  let call : Code Symbol Guard (Value Symbol Guard) := .node child .pure
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure
  have below := mu_request_below source facts holds request scope complete recursive state.machine.domains valid.machine.2
    first second firstIdentity secondIdentity
  obtain ⟨childScope, childComplete, smaller⟩ := below
  have childSmaller : requiredFuel (view source holds) (nodeSemantic child) childComplete <
      requiredFuel (view source holds) (nodeSemantic request) complete := smaller
  have entered := SourceRecursiveIntersectionKernel.entered state.machine valid.machine request.domain ready.1
    request.left request.right ready.2.1 ready.2.2 first second
  have currentValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current :=
    advance_valid width emptyGuard conjoin state valid machine entered.1 entered.2.1
  have childReady : NodeReady current.machine child :=
    ⟨entered.2.2, SourceRecursiveIntersectionKernel.body_available state.machine.heap request.left ready.2.1,
      SourceRecursiveIntersectionKernel.body_available state.machine.heap request.right ready.2.2⟩
  have one : step emptyGuard conjoin (compileMu request.domain request.left request.right) state =
      .yielded (call.bind next) current := by
    simp only [compileMu, firstIdentity, secondIdentity, step]
    rfl
  have afterRanges : WordRanges emptyGuard conjoin (call.bind next) current :=
    ranges.after_step emptyGuard conjoin _ _ _ _ one
  have childRanges : WordRanges emptyGuard conjoin call current :=
    afterRanges.before_bind emptyGuard conjoin call next current
  cases fuel with
  | zero => exact lower_refl state.machine.heap _
  | succ fuel =>
      have lower := execute_bind_lower emptyGuard conjoin fuel call next current
        (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
        (fun inner => (nodeIH child childScope childComplete childSmaller current currentValid childReady
          growth history semantic opened childRanges inner).mono (Nat.add_le_add_left (Nat.le_of_lt childSmaller) limit)) (by
          intro inner bodyValue after done outer
          obtain ⟨_afterValid, _extension, available, bodySemantic, bodyOpened, degree⟩ :=
            node_return_degree_facts source facts limit bounded holds width emptyGuard conjoin inner child
              childScope childComplete current after currentValid childReady growth history semantic opened childRanges bodyValue done
          exact optionalBinder_lower emptyGuard conjoin outer (SourceRecursiveIntersectionControl.pair first second) bodyValue
            after (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
            bodySemantic.1 bodySemantic.2 bodyOpened available (by omega))
      have heapSame : current.machine.heap = state.machine.heap := rfl
      rw [heapSame] at lower
      simpa only [execute, one] using lower

end MicroCFTA.SourceRecursiveIntersectionNative
