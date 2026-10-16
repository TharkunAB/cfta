import MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion

/-!
# Exact return uniqueness for completed raw outer prefixes

Two stable executions meet at the componentwise maximum of ten bounds.
The same literal worker then gives equal results and complete caller states.
Raw prefix graphs supply stable execution through their own completion proof.
No semantic, range, capacity, or future completion premise is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique
open InternedConstructorTemplates SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorkerCompletion
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State

/-- Two stable returns of one literal evaluation agree at ten common larger bounds. -/
theorem stable_unique {A : Type} {width : Nat}
    {evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
      SourceCurrentAllocatedPartialWorker.Outcome A width}
    {first second : A} {after later : Caller width}
    (one : StableRun evaluation first after) (two : StableRun evaluation second later) :
    first = second ∧ after = later := by
  obtain ⟨f, g, s, r, e, p, h, m, c, n, run⟩ := one
  obtain ⟨F, G, S, R, E, P, H, M, C, N, other⟩ := two
  have left := run (max f F) (max g G) (max s S) (max r R) (max e E)
    (max p P) (max h H) (max m M) (max c C) (max n N)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have right := other (max f F) (max g G) (max s S) (max r R) (max e E)
    (max p P) (max h H) (max m M) (max c C) (max n N)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact SourceCurrentAllocatedPartialWorker.Outcome.done.inj (left.symm.trans right)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Two raw node-call prefixes from the same request and state retain the same complete return. -/
theorem node_call {width budget : Nat} {request : NodeRequest}
    {before after later : Caller width} {first second : Node}
    (one : NodeCall budget request before first after) (two : NodeCall budget request before second later) :
    first = second ∧ after = later :=
  stable_unique (nodeCall_complete one) (nodeCall_complete two)

/-- Two raw edge-call prefixes from the same request and state retain the same complete return. -/
theorem edge_call {width budget : Nat} {request : EdgeRequest}
    {before after later : Caller width} {first second : Edge}
    (one : EdgeCall budget request before first after) (two : EdgeCall budget request before second later) :
    first = second ∧ after = later :=
  stable_unique (edgeCall_complete one) (edgeCall_complete two)

/-- Two raw returned-edge descendant prefixes retain the same result and complete caller state. -/
theorem descendants {width budget : Nat} {inherited : SourceEqualityConstraintAllocation.Value}
    {edge first second : Edge} {before after later : Caller width}
    (one : Descendants budget inherited edge before first after)
    (two : Descendants budget inherited edge before second later) :
    first = second ∧ after = later :=
  stable_unique (descendants_complete one) (descendants_complete two)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique
