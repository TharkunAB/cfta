import MicroCFTA.SourceRecursiveIntersectionAnnotationCode

/-!
# Derived annotation conditions of compiled source calls

Actual child requests retain their physical cache scopes. Literal edge work
checks the emitted guard. Node and union work reuse existing physical edges.
Optional binder bodies remain available at their actual source call sites.
-/
namespace MicroCFTA.SourceRecursiveIntersectionAnnotationCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual Mu compilation derives safe body requests and optional-binder effects. -/
theorem compileMu_annotation (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) :
    Certified annotation (compileMu domain left right) state := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;> simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstId secondId
  obtain ⟨afterValid, growth, afterDomain⟩ := entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  refine ⟨⟨afterDomain, body_available _ left leftAvailable, body_available _ right rightAvailable⟩, ?_⟩
  intro value final finalValid later available
  exact annotation_optionalBinder annotation _ value final available

/-- Original free-binding readback supplies the complete next physical node request. -/
theorem compileReference_annotation (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) :
    Certified annotation (compileReference domain name other left) state := by
  by_cases bound : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name bound
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [compileReference, bound, ite_true, Certified, read]
    cases left
    · exact annotation_requestNode annotation domain other (.mu entry body depth ordinary) state ⟨known, available, stored⟩
    · exact annotation_requestNode annotation domain (.mu entry body depth ordinary) other state ⟨known, stored, available⟩
  · simp only [compileReference, bound, ite_false, Certified]

/-- Every guarded compiled edge derives available ordered child requests and a complete output row. -/
theorem compileEdge_annotation (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : EdgeReady state request) : Certified annotation (compileEdge emptyGuard conjoin request) state := by
  unfold compileEdge
  split
  · let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
      Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
    have stable : Stable input := by
      intro before after growth pair known
      exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
    have children := safe_walk (fun pair => requestNode request.domain pair.1 pair.2)
      (request.left.children.zip request.right.children) input _ stable available_stable
      (fun pair _ current currentValid known => safe_requestNode request.domain pair.1 pair.2 current known)
      state valid (by
        intro pair member
        have contained := List.of_mem_zip member
        exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 contained.1,
          valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 contained.2⟩)
    have childrenSemantic := annotation_walk annotation (fun pair => requestNode request.domain pair.1 pair.2)
      (request.left.children.zip request.right.children) input _ stable available_stable
      (fun pair _ current currentValid known => safe_requestNode request.domain pair.1 pair.2 current known)
      (fun pair _ current currentValid known => annotation_requestNode annotation request.domain pair.1 pair.2 current known)
      state valid (by
        intro pair member
        have contained := List.of_mem_zip member
        exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 contained.1,
          valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 contained.2⟩)
    apply annotation_bind annotation _ _ state valid _ children childrenSemantic
    intro values after afterValid growth available
    exact annotation_edge annotation _ _ values after (conjoinedValid _ _)
  · exact annotation_edge annotation _ _ [.empty] state emptyValid

/-- Actual hash-join occurrences derive resident row requests before canonical node construction. -/
theorem compileRows_annotation (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge)
    (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge) :
    Certified annotation (compileRows domain left right) state := by
  let input := fun (current : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap pair.1 ∧ EdgeResident current.heap pair.2
  have stable : Stable input := by
    intro before after growth pair known
    exact ⟨known.1.grows _ growth, edge_grows _ _ growth.heap _ known.2.1, edge_grows _ _ growth.heap _ known.2.2⟩
  have rows := safe_walk (fun pair => requestEdge domain pair.1 pair.2) (pairs left right) input _ stable edge_stable
    (fun pair _ current currentValid known => safe_requestEdge domain pair.1 pair.2 current known)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩)
  have rowsSemantic := annotation_walk annotation (fun pair => requestEdge domain pair.1 pair.2) (pairs left right) input _ stable edge_stable
    (fun pair _ current currentValid known => safe_requestEdge domain pair.1 pair.2 current known)
    (fun pair _ current currentValid known => annotation_requestEdge annotation domain pair.1 pair.2 current known)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩)
  apply annotation_bind annotation _ _ state valid _ rows rowsSemantic
  intro values after afterValid growth resident
  exact annotation_node annotation values after

/-- Ordered compiled union requests retain available members before source union construction. -/
theorem union_annotation (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value) :
    Certified annotation ((walk (fun member => if left then requestNode domain member other else requestNode domain other member) members).bind
      fun values => .work (makeUnion values) .pure) state := by
  let input := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap other ∧ Available current.heap value
  have stable : Stable input := by
    intro before after growth value known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have requests := safe_walk (fun member => if left then requestNode domain member other else requestNode domain other member)
    members input _ stable available_stable (by
      intro member present current currentValid known
      cases left
      · exact safe_requestNode domain other member current ⟨known.1, known.2.1, known.2.2⟩
      · exact safe_requestNode domain member other current ⟨known.1, known.2.2, known.2.1⟩)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩)
  have requestsSemantic := annotation_walk annotation (fun member => if left then requestNode domain member other else requestNode domain other member)
    members input _ stable available_stable (by
      intro member present current currentValid known
      cases left
      · exact safe_requestNode domain other member current ⟨known.1, known.2.1, known.2.2⟩
      · exact safe_requestNode domain member other current ⟨known.1, known.2.2, known.2.1⟩)
    (by
      intro member present current currentValid known
      cases left
      · exact annotation_requestNode annotation domain other member current ⟨known.1, known.2.1, known.2.2⟩
      · exact annotation_requestNode annotation domain member other current ⟨known.1, known.2.2, known.2.1⟩)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩)
  apply annotation_bind annotation _ _ state valid _ requests requestsSemantic
  intro values after afterValid growth present
  exact annotation_union annotation values after

end MicroCFTA.SourceRecursiveIntersectionAnnotationCode
