import MicroCFTA.SourceRecursiveIntersectionCodeBounds

/-!
# Strict request limits of compiled physical edges

Equal-arity rows retain every ordered original child request. Each child
has a smaller least semantic bound. The continuation uses the actual
returned source machine. Arity mismatch emits no recursive request.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open InternedNestedFacts

/-- Every compiled original edge body derives its strict request limit and original scope. -/
theorem compileEdge_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (sourceFacts : Facts source) (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : EdgeReady state request) :
    Below source holds (requiredFuel (view source holds) (edgeSemantic holds request) complete)
      (compileEdge emptyGuard conjoin request) state := by
  let bound := requiredFuel (view source holds) (edgeSemantic holds request) complete
  by_cases sameArity : request.left.children.length = request.right.children.length
  · simp only [compileEdge, sameArity, ite_true]
    have childBound (children : Value Symbol Guard × Value Symbol Guard)
        (member : children ∈ request.left.children.zip request.right.children) :
        NodeBelow source holds bound ⟨request.domain, children.1, children.2⟩ := by
      refine ⟨scope.child source sourceFacts request children member, ?_⟩
      apply immediate_requiredFuel (view source holds) (edgeSemantic holds request) _ complete
      apply Immediate.edge (SourceRecursiveIntersectionSchedule.domain request.domain.key) (row holds request.left) (row holds request.right)
        (inputOf children.1, inputOf children.2)
      · simpa only [row, List.length_map] using sameArity
      · change (inputOf children.1, inputOf children.2) ∈
          (request.left.children.map inputOf).zip (request.right.children.map inputOf)
        rw [List.zip_map]
        exact List.mem_map.mpr ⟨children, member, rfl⟩
    let input := fun (current : Machine Symbol Guard) (children : Value Symbol Guard × Value Symbol Guard) =>
      Domain current request.domain ∧ Available current.heap children.1 ∧ Available current.heap children.2
    have stable : Stable input := by
      intro before after growth children known
      exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
    have inputs : ∀ children ∈ request.left.children.zip request.right.children, input state children := by
      intro children member
      have inside := List.of_mem_zip member
      exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 children.1 inside.1,
        valid.1.cached.edges request.right.entry.key request.right ready.2.2 children.2 inside.2⟩
    have calls : ∀ children ∈ request.left.children.zip request.right.children, ∀ current,
        SourceRecursiveIntersectionKernel.Valid current → input current children →
          Safe (requestNode request.domain children.1 children.2) current (fun after value => Available after.heap value) := by
      intro children _ current _ known
      exact safe_requestNode request.domain children.1 children.2 current known
    have built := safe_walk (fun children => requestNode request.domain children.1 children.2)
      (request.left.children.zip request.right.children) input _ stable available_stable calls state valid inputs
    have bounded := below_walk source holds bound (fun children => requestNode request.domain children.1 children.2)
      (request.left.children.zip request.right.children) input _ stable available_stable calls
      (fun children member current _ _ => below_requestNode source holds bound _ current (childBound children member)) state valid inputs
    exact below_bind source holds bound _ _ state valid _ built bounded
      (fun values after _ _ _ => below_work source holds bound _ after)
  · simp only [compileEdge, sameArity, ite_false]
    exact below_work source holds bound _ state

end MicroCFTA.SourceRecursiveIntersectionCode
