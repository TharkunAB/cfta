import MicroCFTA.InternedFreshOrdinaryNodeCounterGrowth
import MicroCFTA.SourceRecursiveIntersectionMaybeMu

namespace MicroCFTA.InternedFreshOrdinaryStoredNodeCounterGrowth
open InternedConstructorTemplates
open InternedNestedConstruction (Outcome work request)
open InternedStoredSubstitution (Environment)
open InternedBinderProtocol (Reference)
variable {Symbol Guard First Result : Type}

/-- Sequential completed or pending outcomes retain the node supply. -/
private theorem bind_mono (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (state : State Symbol Guard)
    (first : state.nodes.next ≤ outcome.state.nodes.next)
    (later : ∀ value current, current.nodes.next ≤ (next value current).state.nodes.next) :
    state.nodes.next ≤ (outcome.bind next).state.nodes.next := by
  cases outcome with
  | done value current => exact Nat.le_trans first (later value current)
  | pending key current => exact first

/-- Actual stored substitution and cleanup retain the node supply. -/
private theorem callback_mono [DecidableEq (EdgeKey Symbol Guard)] (old : Reference)
    (body : Value Symbol Guard) (name : Reference) (state : State Symbol Guard) :
    state.nodes.next ≤
      (SourceRecursiveIntersectionMaybeMu.callback old body name state).state.nodes.next := by
  unfold SourceRecursiveIntersectionMaybeMu.callback
  apply bind_mono _ _ state (InternedFreshOrdinaryNodeCounterGrowth.build_mono _ _ state)
  intro value after
  simp only [work, Outcome.state]
  rw [(SourceCurrentAllocatedFiniteOrdinaryReservations.run_next
    (withoutSelfReference name value) after).1]
  omega

/-- The actual canonical request retains the node supply for its stored callback. -/
private theorem request_mono [DecidableEq (EdgeKey Symbol Guard)] (old : Reference)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) :
    state.nodes.next ≤
      (request true depth ordinary (SourceRecursiveIntersectionMaybeMu.callback old body) state).state.nodes.next := by
  have reserved : state.nodes.next ≤ (Cache.intern state.nodes (muKey depth ordinary)).2.next := by
    rw [SourceCurrentAllocatedFiniteOrdinaryReservations.intern_next]
    omega
  simp only [request]
  split
  · split <;> exact Nat.le_refl _
  · apply bind_mono _ _ state
    · exact Nat.le_trans reserved
        (callback_mono old body (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
          {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2})
    · intro bodyValue afterBody
      exact Nat.le_refl _

/-- Actual repaired stored substitution retains the node supply on every outcome. -/
theorem execute_mono [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) :
    state.nodes.next ≤ (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state.nodes.next := by
  exact InternedFreshOrdinaryNodeCounterGrowth.build_mono _ _ state

/-- Actual repaired unfolding retains the node supply on every outcome. -/
theorem unfold_mono [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) :
    state.nodes.next ≤ (InternedFreshOrdinaryStoredSubstitution.unfold value state).state.nodes.next := by
  cases value with
  | mu entry body depth ordinary => exact execute_mono body _ state
  | empty | reference | node | union => exact Nat.le_refl _

/-- Actual optional binder construction retains the node supply on every outcome. -/
theorem maybeMu_mono [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (state : State Symbol Guard) :
    state.nodes.next ≤ (SourceRecursiveIntersectionMaybeMu.maybeMu key body state).state.nodes.next := by
  simp only [SourceRecursiveIntersectionMaybeMu.maybeMu]
  split
  · simp only [SourceRecursiveIntersectionMaybeMu.construct]
    apply bind_mono _ _ state (callback_mono _ _ .depth state)
    intro depth afterDepth
    apply bind_mono _ _ afterDepth
      (callback_mono _ _ (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth)
    intro ordinary afterOrdinary
    exact request_mono _ _ depth ordinary afterOrdinary
  · exact Nat.le_refl _

end MicroCFTA.InternedFreshOrdinaryStoredNodeCounterGrowth
