import MicroCFTA.SourceRecursiveIntersectionScopeCalls

/-!
# Recursive result scope through actual guarded rows and unions

Ordered child and row calls retain their actual returned semantic heaps.
Guarded edge construction and canonical node normalization retain only
those child names. Union reconstruction retains the same incoming scope.
-/
namespace MicroCFTA.SourceRecursiveIntersectionScopeCalls
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceRecursiveIntersectionScopeEffects (Observed)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual guarded edge execution retains only incoming recursive pair names in its ordered children. -/
theorem edge_scoped [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : ScopedCalls call) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right) (heap : SemanticHeap state.heap) :
    Observed (edge emptyGuard conjoin (call domain) left right state) (EdgeScope domain.key.seen) := by
  unfold edge
  split
  · have inputs : ∀ pair ∈ left.children.zip right.children, Available state.heap pair.1 ∧ Available state.heap pair.2 := by
      intro pair member
      have contained := List.of_mem_zip member
      exact ⟨valid.1.cached.edges left.entry.key left leftResident pair.1 contained.1,
        valid.1.cached.edges right.entry.key right rightResident pair.2 contained.2⟩
    have physical := children_checked call calls domain _ state valid known inputs
    have observed := children_scoped call calls scopes domain _ state valid known inputs heap
    apply SourceRecursiveIntersectionScopeEffects.bind _ _ _ _ observed
    intro values after done afterHeap scope
    exact SourceRecursiveIntersectionScopeEffects.edge_observed domain.key.seen left.entry.key.symbol
      (conjoin left.entry.key.constraint right.entry.key.constraint) values after afterHeap (physical.result _ _ done) scope
  · apply SourceRecursiveIntersectionScopeEffects.edge_observed domain.key.seen left.entry.key.symbol emptyGuard [.empty] state heap
    · intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact empty_available state.heap
    · intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact SourceRecursiveIntersectionResultScope.closed _ _ rfl

/-- Actual ordered matched rows retain their semantic heaps and incoming pair scope. -/
theorem rows_scoped [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : ScopedCalls call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (heap : SemanticHeap state.heap) :
    Observed (walk (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) state)
      (fun edges => ∀ edge ∈ edges, EdgeScope domain.key.seen edge) := by
  let input := fun (current : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap pair.1 ∧ EdgeResident current.heap pair.2
  have stable : Stable input := by
    intro before after growth pair known
    exact ⟨known.1.grows _ growth, edge_grows _ _ growth.heap _ known.2.1, edge_grows _ _ growth.heap _ known.2.2⟩
  exact SourceRecursiveIntersectionScopeEffects.walk_observed
    (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) input
    (fun after value => EdgeResident after.heap value) (EdgeScope domain.key.seen) stable
    (fun pair _ current currentValid known => edge_checked emptyGuard conjoin call calls domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    (fun pair _ current currentValid known => edge_scoped emptyGuard conjoin call calls scopes domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩) heap

/-- Actual ordered rows and canonical node construction derive the incoming recursive result scope. -/
theorem node_scoped [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : ScopedCalls call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (heap : SemanticHeap state.heap) : Observed (node emptyGuard conjoin (call domain) left right state) (Scope domain.key.seen) := by
  have physical := rows_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  have observed := rows_scoped emptyGuard conjoin call calls scopes domain left right state valid known leftResident rightResident heap
  rw [node]
  apply SourceRecursiveIntersectionScopeEffects.bind _ _ _ _ observed
  intro edges after done afterHeap scope
  exact SourceRecursiveIntersectionScopeEffects.node_observed domain.key.seen edges after afterHeap (physical.result _ _ done) scope

/-- Actual ordered union calls and normalization retain only incoming recursive pair names. -/
theorem union_scoped [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : ScopedCalls call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value)
    (heap : SemanticHeap state.heap) :
    Observed ((walk (fun member => if left then call domain member other else call domain other member) members state).bind
      fun values after => work (makeUnion values) after) (Scope domain.key.seen) := by
  let input := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap other ∧ Available current.heap value
  have stable : Stable input := by
    intro before after growth value known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have physical := walk_checked (fun member => if left then call domain member other else call domain other member) members input
    (fun after value => Available after.heap value) stable available_stable (by
      intro member present current currentValid known
      cases left
      · exact calls domain other member current currentValid known.1 known.2.1 known.2.2
      · exact calls domain member other current currentValid known.1 known.2.2 known.2.1)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩)
  have observed := SourceRecursiveIntersectionScopeEffects.walk_observed
    (fun member => if left then call domain member other else call domain other member) members input
    (fun after value => Available after.heap value) (Scope domain.key.seen) stable (by
      intro member present current currentValid known
      cases left
      · exact calls domain other member current currentValid known.1 known.2.1 known.2.2
      · exact calls domain member other current currentValid known.1 known.2.2 known.2.1)
    (by
      intro member present current currentValid known
      cases left
      · exact scopes domain other member current currentValid known.1 known.2.1 known.2.2
      · exact scopes domain member other current currentValid known.1 known.2.2 known.2.1)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩) heap
  apply SourceRecursiveIntersectionScopeEffects.bind _ _ _ _ observed
  intro values after done afterHeap scope
  exact SourceRecursiveIntersectionScopeEffects.union_observed domain.key.seen values after afterHeap (physical.result _ _ done) scope

end MicroCFTA.SourceRecursiveIntersectionScopeCalls
