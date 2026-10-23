import MicroCFTA.InternedFreshOrdinaryGrowth
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations

namespace MicroCFTA.InternedFreshOrdinaryNodeCounterGrowth
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction
variable {Symbol Guard First Result : Type}

/-- Actual Work cannot reduce the node supply. -/
private theorem work_mono [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : State Symbol Guard) :
    state.nodes.next ≤ (run computation state).2.nodes.next := by
  rw [(SourceCurrentAllocatedFiniteOrdinaryReservations.run_next computation state).1]
  omega

/-- Sequential outcomes retain the node supply on completion or pending return. -/
private theorem bind_mono (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (state : State Symbol Guard)
    (first : state.nodes.next ≤ outcome.state.nodes.next)
    (later : ∀ value current, current.nodes.next ≤ (next value current).state.nodes.next) :
    state.nodes.next ≤ (outcome.bind next).state.nodes.next := by
  cases outcome with
  | done value current => exact Nat.le_trans first (later value current)
  | pending key current => exact first

/-- Actual Mu request branches retain the node supply through their callback. -/
private theorem request_mono [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard →
      Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard)
    (later : ∀ name current, current.nodes.next ≤ (callback name current).state.nodes.next) :
    state.nodes.next ≤ (request smart depth ordinary callback state).state.nodes.next := by
  have reserved : state.nodes.next ≤ (Cache.intern state.nodes (muKey depth ordinary)).2.next := by
    rw [SourceCurrentAllocatedFiniteOrdinaryReservations.intern_next]
    omega
  simp only [request]
  split
  · split <;> exact Nat.le_refl _
  · apply bind_mono _ _ state
    · exact Nat.le_trans reserved
        (later (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
          {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2})
    · intro bodyValue afterBody
      exact Nat.le_refl _

mutual
/-- Actual repaired construction retains the node supply on every outcome. -/
theorem build_mono [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    state.nodes.next ≤ (build expression environment state).state.nodes.next := by
  cases expression with
  | empty | var index => simp only [build, Outcome.state]; exact Nat.le_refl _
  | node edges =>
      simp only [build]
      exact bind_mono _ _ state (buildEdges_mono edges environment state)
        (fun values current => work_mono (makeNode values) current)
  | union members =>
      simp only [build]
      exact bind_mono _ _ state (buildMany_mono members environment state)
        (fun values current => work_mono (makeUnion values) current)
  | binder smart body =>
      let callback : InternedBinderProtocol.Reference → State Symbol Guard →
          Outcome Symbol Guard (Value Symbol Guard) :=
        fun name current => (build body (.reference name :: environment) current).bind
          fun value next => work (withoutSelfReference name value) next
      have preserved : ∀ name current,
          current.nodes.next ≤ (callback name current).state.nodes.next := by
        intro name current
        exact bind_mono _ _ current (build_mono body (.reference name :: environment) current)
          (fun value after => work_mono (withoutSelfReference name value) after)
      simp only [build]
      apply bind_mono _ _ state (preserved .depth state)
      intro depth afterDepth
      apply bind_mono _ _ afterDepth (preserved (.uninterned (ordinaryLevel depth)) afterDepth)
      intro ordinary afterOrdinary
      exact request_mono smart depth ordinary callback afterOrdinary preserved
termination_by sizeOf expression

/-- Actual ordered child construction retains the node supply on every outcome. -/
theorem buildMany_mono [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    state.nodes.next ≤ (buildMany expression environment state).state.nodes.next := by
  cases expression with
  | nil => simp only [buildMany, Outcome.state]; exact Nat.le_refl _
  | cons first rest =>
      simp only [buildMany]
      apply bind_mono _ _ state (build_mono first environment state)
      intro value next
      apply bind_mono _ _ next (buildMany_mono rest environment next)
      intro values final
      exact Nat.le_refl _
termination_by sizeOf expression

/-- Actual ordered edge construction retains the node supply on every outcome. -/
theorem buildEdges_mono [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    state.nodes.next ≤ (buildEdges expression environment state).state.nodes.next := by
  cases expression with
  | nil => simp only [buildEdges, Outcome.state]; exact Nat.le_refl _
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges]
          apply bind_mono _ _ state (buildMany_mono children environment state)
          intro values next
          apply bind_mono (work (makeEdge symbol constraint values) next) _ next
            (work_mono (makeEdge symbol constraint values) next)
          intro edge afterEdge
          apply bind_mono _ _ afterEdge (buildEdges_mono rest environment afterEdge)
          intro edges final
          exact Nat.le_refl _
termination_by sizeOf expression
end

end MicroCFTA.InternedFreshOrdinaryNodeCounterGrowth
