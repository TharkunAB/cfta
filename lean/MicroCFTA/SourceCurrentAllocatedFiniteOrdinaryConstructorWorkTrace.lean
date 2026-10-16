import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations

/-!
# Actual constructor Work traces

Each Work entry records its real initial heap and observed request list.
Composition retains the exact intermediate heap and request order.
Request counts bound reservation counts and both constructor supplies.
These traces do not model host scheduling or unrelated allocations.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryReservations
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Record literal Work jobs and their actual intermediate constructor heaps. -/
inductive Trace : State Symbol Guard → State Symbol Guard → List (Request Symbol Guard) → Prop where
  | refl (state : State Symbol Guard) : Trace state state []
  | work (state : State Symbol Guard) (job : Work Symbol Guard Result) :
      Trace state (run job state).2 (observe job state)
  | trans (first : Trace before middle earlier) (last : Trace middle after later) :
      Trace before after (earlier ++ later)

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- Concatenation retains every observed node request. -/
theorem nodeRequests_append (first last : List (Request Symbol Guard)) :
    nodeRequests (first ++ last) = nodeRequests first + nodeRequests last := by
  induction first with
  | nil => simp [nodeRequests]
  | cons request rest ih => cases request <;> simp [nodeRequests, ih, Nat.add_assoc]

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- Concatenation retains every observed edge request. -/
theorem edgeRequests_append (first last : List (Request Symbol Guard)) :
    edgeRequests (first ++ last) = edgeRequests first + edgeRequests last := by
  induction first with
  | nil => simp [edgeRequests]
  | cons request rest ih => cases request <;> simp [edgeRequests, ih, Nat.add_assoc]

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- Concatenation retains every observed node reservation. -/
theorem nodeReservations_append (first last : List (Request Symbol Guard)) :
    nodeReservations (first ++ last) = nodeReservations first + nodeReservations last := by
  induction first with
  | nil => simp [nodeReservations]
  | cons request rest ih => cases request <;> simp [nodeReservations, ih, Nat.add_assoc]

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- Concatenation retains every observed edge reservation. -/
theorem edgeReservations_append (first last : List (Request Symbol Guard)) :
    edgeReservations (first ++ last) = edgeReservations first + edgeReservations last := by
  induction first with
  | nil => simp [edgeReservations]
  | cons request rest ih => cases request <;> simp [edgeReservations, ih, Nat.add_assoc]

/-- Both counters equal the initial supply plus the actual recorded misses. -/
theorem Trace.next_exact {before after : State Symbol Guard} {requests : List (Request Symbol Guard)}
    (trace : Trace before after requests) :
    after.nodes.next = before.nodes.next + nodeReservations requests ∧
    after.edges.next = before.edges.next + edgeReservations requests := by
  induction trace with
  | refl => simp [nodeReservations, edgeReservations]
  | work => exact run_next _ _
  | trans first last firstIH lastIH =>
      rw [nodeReservations_append, edgeReservations_append]
      constructor <;> omega

/-- Actual constructor requests bound both returned supplies. -/
theorem Trace.next_le {before after : State Symbol Guard} {requests : List (Request Symbol Guard)}
    (trace : Trace before after requests) :
    after.nodes.next ≤ before.nodes.next + nodeRequests requests ∧
    after.edges.next ≤ before.edges.next + edgeRequests requests := by
  have counts := trace.next_exact
  have bounded := reservations_le_requests requests
  constructor <;> omega

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace
