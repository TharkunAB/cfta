import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEntries
import MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ReachAudit
open InternedConstructorTemplates SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorkerCompletion
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
private theorem stable_unique {A : Type} {width : Nat}
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

theorem node_prefix_unique {width budget : Nat} {request : NodeRequest}
    {before after later : Caller width} {first second : Node}
    (one : NodeCall budget request before first after) (two : NodeCall budget request before second later) :
    first = second ∧ after = later :=
  stable_unique (nodeCall_complete one) (nodeCall_complete two)

theorem edge_prefix_unique {width budget : Nat} {request : EdgeRequest}
    {before after later : Caller width} {first second : Edge}
    (one : EdgeCall budget request before first after) (two : EdgeCall budget request before second later) :
    first = second ∧ after = later :=
  stable_unique (edgeCall_complete one) (edgeCall_complete two)

theorem descendant_prefix_unique {width budget : Nat}
    {inherited : SourceEqualityConstraintAllocation.Value} {edge first second : Edge}
    {before after later : Caller width}
    (one : Descendants budget inherited edge before first after)
    (two : Descendants budget inherited edge before second later) :
    first = second ∧ after = later :=
  stable_unique (descendants_complete one) (descendants_complete two)

theorem two_row_prefixes_join {width budget : Nat}
    {inherited : SourceEqualityConstraintAllocation.Value} {original narrowed other result second : Edge}
    {before middle alternate after later : Caller width}
    (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (otherEdge : EdgeCall budget ⟨inherited, original⟩ before other alternate)
    (children : Descendants budget inherited narrowed middle result after)
    (otherChildren : Descendants budget inherited other alternate second later) :
    narrowed = other ∧ middle = alternate ∧ result = second ∧ after = later := by
  obtain ⟨sameEdge, sameState⟩ := edge_prefix_unique edge otherEdge
  subst other
  subst alternate
  exact ⟨rfl, rfl, descendant_prefix_unique children otherChildren⟩

#print axioms node_prefix_unique
#check @node_prefix_unique
#print axioms edge_prefix_unique
#check @edge_prefix_unique
#print axioms descendant_prefix_unique
#check @descendant_prefix_unique
#print axioms two_row_prefixes_join
#check @two_row_prefixes_join

end MicroCFTA.ReachAudit
