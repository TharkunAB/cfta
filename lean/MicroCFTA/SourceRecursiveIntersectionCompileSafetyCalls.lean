import MicroCFTA.SourceRecursiveIntersectionCodeSafety

/-!
# Physical safety of compiled recursive source calls

Actual domain entry, original binder reads, guarded child requests, matched
rows, and ordered unions derive continuation safety. Constructor verification
supplies the complete returned physical records. No memo completion or
product-language law is assumed.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks

/-- Actual Mu compilation derives safe body requests and optional-binder effects. -/
theorem compileMu_safe [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) :
    Safe (compileMu domain left right) state (fun after value => Available after.heap value) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;> simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstId secondId
  obtain ⟨afterValid, growth, afterDomain⟩ := entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  refine ⟨afterValid, growth, ⟨afterDomain, body_available _ left leftAvailable, body_available _ right rightAvailable⟩, ?_⟩
  intro value final finalValid later available
  exact safe_optionalBinder _ value final finalValid available

/-- Original free-binding readback supplies the complete next physical node request. -/
theorem compileReference_safe [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) :
    Safe (compileReference domain name other left) state (fun after value => Available after.heap value) := by
  by_cases bound : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name bound
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [compileReference, bound, ite_true, Safe, read]
    cases left
    · exact safe_requestNode domain other (.mu entry body depth ordinary) state ⟨known, available, stored⟩
    · exact safe_requestNode domain (.mu entry body depth ordinary) other state ⟨known, stored, available⟩
  · simp only [compileReference, bound, ite_false, Safe]

/-- Every guarded compiled edge derives available ordered child requests and a complete output row. -/
theorem compileEdge_safe [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : EdgeReady state request) : Safe (compileEdge emptyGuard conjoin request) state (fun after value => EdgeResident after.heap value) := by
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
    apply safe_bind _ _ state valid _ _ children
    intro values after afterValid growth available
    exact safe_work _ after afterValid EdgeResident (InternedNestedFacts.edge_verified _ _ values after.heap afterValid.1 available)
  · exact safe_work _ state valid EdgeResident
      (InternedNestedFacts.edge_verified _ _ [.empty] state.heap valid.1
        (by intro value member; simp only [List.mem_singleton] at member; subst value; exact empty_available state.heap))

/-- Actual hash-join occurrences derive resident row requests before canonical node construction. -/
theorem compileRows_safe [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge)
    (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge) :
    Safe (compileRows domain left right) state (fun after value => Available after.heap value) := by
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
  apply safe_bind _ _ state valid _ _ rows
  intro values after afterValid growth resident
  exact safe_work _ after afterValid Available (InternedNestedFacts.node_verified values after.heap afterValid.1 resident)

/-- Ordered compiled union requests retain available members before source union construction. -/
theorem union_safe [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value) :
    Safe ((walk (fun member => if left then requestNode domain member other else requestNode domain other member) members).bind
      fun values => .work (makeUnion values) .pure) state (fun after value => Available after.heap value) := by
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
  apply safe_bind _ _ state valid _ _ requests
  intro values after afterValid growth present
  exact safe_work _ after afterValid Available (InternedNestedFacts.union_verified values after.heap afterValid.1 present)

end MicroCFTA.SourceRecursiveIntersectionCode
