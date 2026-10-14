import MicroCFTA.SourceRecursiveIntersectionScopeEffects

/-!
# Recursive pair scope through actual Mu, reference, and child calls

Actual Mu entry adds one recursive pair to the canonical domain. The body
return retains its semantic heap. Actual optional-binder construction then
removes that pair. Reference lookup and ordered child requests retain the
incoming pair scope without replacing physical calls or caches.
-/
namespace MicroCFTA.SourceRecursiveIntersectionScopeCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceRecursiveIntersectionScopeEffects (Observed)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Recursive calls derive result scope and retained semantic heaps at every actual successful return. -/
def ScopedCalls
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ domain left right (state : Machine Symbol Guard), SourceRecursiveIntersectionKernel.Valid state → Domain state domain →
    Available state.heap left → Available state.heap right → SemanticHeap state.heap →
    Observed (call domain left right state) (Scope domain.key.seen)

/-- Actual Mu entry and optional-binder execution retain only the incoming domain's possible pair names. -/
theorem mu_scoped [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : ScopedCalls call) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) (heap : SemanticHeap state.heap) :
    Observed (mu call domain left right state) (Scope domain.key.seen) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;> simp only [mu, first, second]
  all_goals try exact SourceRecursiveIntersectionScopeEffects.failed _ state _
  rename_i firstId secondId
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right firstId secondId
  let after : Machine Symbol Guard := {state with domains := actual.2}
  obtain ⟨afterValid, growth, afterDomain⟩ := entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  have requested := calls actual.1 (body left) (body right) after afterValid afterDomain
    (body_available state.heap left leftAvailable) (body_available state.heap right rightAvailable)
  have observed := scopes actual.1 (body left) (body right) after afterValid afterDomain
    (body_available state.heap left leftAvailable) (body_available state.heap right rightAvailable) heap
  apply SourceRecursiveIntersectionScopeEffects.bind _ _ _ _ observed
  intro value final done finalHeap scope
  have available := requested.result value final done
  have key : actual.1.key = extend domain.key ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair firstId secondId) :=
    (SourceRecursiveIntersectionEnvironment.enter_correct state.heap state.domains valid.2 domain.key known.bindings left right
      leftAvailable rightAvailable firstId secondId).2.1.1
  have bodyScope : Scope (SourceRecursiveIntersectionControl.pair firstId secondId :: domain.key.seen) value := by
    apply SourceRecursiveIntersectionResultScope.weaken actual.1.key.seen _ ?_ value scope
    intro next member
    rw [key] at member
    rcases (extend_seen _ _ _ next).mp member with same | old
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons.mpr (Or.inr old)
  exact SourceRecursiveIntersectionScopeEffects.optional_observed domain.key.seen
    (SourceRecursiveIntersectionControl.pair firstId secondId) value final finalHeap available bodyScope

/-- Actual original binding lookup retains the recursive result scope of its next source call. -/
theorem reference_scoped
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (scopes : ScopedCalls call) (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (available : Available state.heap other) (heap : SemanticHeap state.heap) :
    Observed (reference call domain name other left state) (Scope domain.key.seen) := by
  by_cases bound : name ∈ names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name bound
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [reference, bound, ite_true, read]
    cases left
    · exact scopes domain other (.mu entry body depth ordinary) state valid known available stored heap
    · exact scopes domain (.mu entry body depth ordinary) other state valid known stored available heap
  · simp only [reference, bound, ite_false]
    exact SourceRecursiveIntersectionScopeEffects.failed _ state _

/-- Ordered actual child calls retain their complete semantic heaps and incoming recursive pair scope. -/
theorem children_scoped
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : ScopedCalls call) (domain : Interned DomainKey) (requests : List (Value Symbol Guard × Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (inputs : ∀ pair ∈ requests, Available state.heap pair.1 ∧ Available state.heap pair.2) (heap : SemanticHeap state.heap) :
    Observed (walk (fun pair => call domain pair.1 pair.2) requests state) (fun values => ∀ value ∈ values, Scope domain.key.seen value) := by
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have stable : Stable input := by
    intro before after growth pair known
    exact ⟨known.1.grows domain growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  exact SourceRecursiveIntersectionScopeEffects.walk_observed (fun pair => call domain pair.1 pair.2) requests input
    (fun after value => Available after.heap value) (Scope domain.key.seen) stable
    (fun pair _ current currentValid known => calls domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    (fun pair _ current currentValid known => scopes domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    state valid (fun pair member => ⟨known, inputs pair member⟩) heap

end MicroCFTA.SourceRecursiveIntersectionScopeCalls
