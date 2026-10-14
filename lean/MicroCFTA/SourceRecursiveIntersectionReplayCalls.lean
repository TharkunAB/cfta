import MicroCFTA.SourceRecursiveIntersectionReplayEffects

/-!
# Replay of actual ordered recursive requests

Original domain bindings, union requests, guarded children, and matched
rows replay their exact completed values after later caller effects.
Canonical constructor replay then leaves both later caches unchanged.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionDomain

/-- Completed original-bound-variable requests replay their exact source lookup and child result. -/
theorem reference_replay
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard)
    (left : Bool) (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (available : Available before.heap other) (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : reference call domain name other left before = .done value final) (growth : Extension final after) :
    reference call domain name other left after = .done value after := by
  have checked := reference_checked call calls domain name other left before valid known available
  have earlier : Extension before final := by simpa only [done, Result.state] using checked.extension
  by_cases bound : name ∈ names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name bound
    have original := SourcePreparedSharedRows.read_identity before.heap valid.1 _ stored entry.identity rfl
    have current := read_grows before after (earlier.trans growth) entry.identity _ original
    simp only [reference, bound, ite_true, original] at done
    simp only [reference, bound, ite_true, current]
    cases left
    · exact replay domain other (.mu entry body depth ordinary) before after value final valid known available stored done growth
    · exact replay domain (.mu entry body depth ordinary) other before after value final valid known stored available done growth
  · simp only [reference, bound, ite_false] at done
    cases done

/-- Guarded child calls and actual canonical edge construction replay without another allocation. -/
theorem edge_replay [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftResident : EdgeResident before.heap left) (rightResident : EdgeResident before.heap right)
    (value : EdgeValue Symbol Guard) (final : Machine Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right before = .done value final) (growth : Extension final after) :
    edge emptyGuard conjoin (call domain) left right after = .done value after := by
  by_cases arity : left.children.length = right.children.length
  · simp only [edge, arity, ite_true] at done ⊢
    let input := fun (state : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
      Domain state domain ∧ Available state.heap pair.1 ∧ Available state.heap pair.2
    have stable : Stable input := by
      intro before after extension pair known
      exact ⟨known.1.grows domain extension, extension.available _ known.2.1, extension.available _ known.2.2⟩
    have inputs : ∀ pair ∈ left.children.zip right.children, input before pair := by
      intro pair member
      have contained := List.of_mem_zip member
      exact ⟨known, valid.1.cached.edges left.entry.key left leftResident pair.1 contained.1,
        valid.1.cached.edges right.entry.key right rightResident pair.2 contained.2⟩
    have checked := children_checked call calls domain (left.children.zip right.children) before valid known
      (fun pair member => (inputs pair member).2)
    apply bind_work_replay _ _ before after _ checked _ value final done growth
    intro values middle returned later
    exact walk_replay (fun pair => call domain pair.1 pair.2) (left.children.zip right.children) input _ stable available_stable
      (fun pair _ state valid known => calls domain pair.1 pair.2 state valid known.1 known.2.1 known.2.2)
      (fun pair _ before after value final valid known =>
        replay domain pair.1 pair.2 before after value final valid known.1 known.2.1 known.2.2)
      before after values middle valid inputs returned later
  · simp only [edge, arity, ite_false] at done ⊢
    exact work_replay _ before after value final valid done growth

/-- Matched source row occurrences and canonical node construction replay in the unchanged later caches. -/
theorem node_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftResident : ∀ edge ∈ left, EdgeResident before.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident before.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right before = .done value final) (growth : Extension final after) :
    node emptyGuard conjoin (call domain) left right after = .done value after := by
  let input := fun (state : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain state domain ∧ EdgeResident state.heap pair.1 ∧ EdgeResident state.heap pair.2
  have stable : Stable input := by
    intro before after extension pair known
    exact ⟨known.1.grows domain extension, InternedEdgeResidency.edge_grows _ _ extension.heap _ known.2.1,
      InternedEdgeResidency.edge_grows _ _ extension.heap _ known.2.2⟩
  have inputs : ∀ pair ∈ pairs left right, input before pair := by
    intro pair member
    obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
    exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩
  have checked := rows_checked emptyGuard conjoin call calls domain left right before valid known leftResident rightResident
  simp only [node] at done ⊢
  apply bind_work_replay _ _ before after _ checked _ value final done growth
  intro values middle returned later
  exact walk_replay (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) input _ stable edge_stable
    (fun pair _ state valid known => edge_checked emptyGuard conjoin call calls domain pair.1 pair.2 state valid known.1 known.2.1 known.2.2)
    (fun pair _ before after value final valid known =>
      edge_replay emptyGuard conjoin call calls replay domain pair.1 pair.2 before after valid known.1 known.2.1 known.2.2 value final)
    before after values middle valid inputs returned later

/-- Ordered union members and actual union construction replay their complete source result. -/
theorem union_replay [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (available : Available before.heap other) (membersAvailable : ∀ member ∈ members, Available before.heap member)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members before).bind
      (fun values current => work (makeUnion values) current) = .done value final) (growth : Extension final after) :
    (walk (fun member => if left then call domain member other else call domain other member) members after).bind
      (fun values current => work (makeUnion values) current) = .done value after := by
  let input := fun (state : Machine Symbol Guard) (member : Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap other ∧ Available state.heap member
  have stable : Stable input := by
    intro before after extension member known
    exact ⟨known.1.grows domain extension, extension.available _ known.2.1, extension.available _ known.2.2⟩
  have checkedCalls : ∀ member ∈ members, ∀ state, Valid state → input state member →
      Checked state ((if left then call domain member other else call domain other member) state) (fun after value => Available after.heap value) := by
    intro member _ state valid known
    cases left
    · exact calls domain other member state valid known.1 known.2.1 known.2.2
    · exact calls domain member other state valid known.1 known.2.2 known.2.1
  have replayCalls : ∀ member ∈ members, ∀ before after value final, Valid before → input before member →
      (if left then call domain member other else call domain other member) before = .done value final → Extension final after →
      (if left then call domain member other else call domain other member) after = .done value after := by
    intro member _ before after value final valid known
    cases left
    · exact replay domain other member before after value final valid known.1 known.2.1 known.2.2
    · exact replay domain member other before after value final valid known.1 known.2.2 known.2.1
  have inputs : ∀ member ∈ members, input before member := fun member present => ⟨known, available, membersAvailable member present⟩
  have checked := walk_checked _ members input _ stable available_stable checkedCalls before valid inputs
  apply bind_work_replay _ _ before after _ checked _ value final done growth
  intro values middle returned later
  exact walk_replay _ members input _ stable available_stable checkedCalls replayCalls before after values middle valid inputs returned later

end MicroCFTA.SourceRecursiveIntersectionKernel
