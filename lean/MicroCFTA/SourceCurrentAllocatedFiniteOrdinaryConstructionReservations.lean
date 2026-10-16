import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstruction
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations

/-!
# Static reservation bounds for ordinary source construction

Count syntax nodes and rows, including all nested child syntax.
Empty and variable syntax make no request.
The proof constructs the same actual source return from any initial heap.
Binder and union syntax remain outside the stated source domain.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructionReservations
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedFacts (Facts)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedFiniteOrdinaryReservations (makeNode_next makeEdge_next)
local notation "SourceNode" => SourceCurrentAllocatedFiniteOrdinaryConstruction.Node
local notation "SourceChildren" => SourceCurrentAllocatedFiniteOrdinaryConstruction.Children
local notation "SourceRows" => SourceCurrentAllocatedFiniteOrdinaryConstruction.Rows
local notation "Domain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Domains" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

mutual
/-- Count ordinary node and row occurrences; unsupported constructors contribute zero. -/
def counts : Syntax Symbol Guard → Nat × Nat
  | .empty | .var _ | .binder .. | .union _ => (0, 0)
  | .node edges => (1 + (countsRows edges).1, (countsRows edges).2)
termination_by expression => sizeOf expression

/-- Add counts at every literal child position, including repeated syntax. -/
def countsMany : List (Syntax Symbol Guard) → Nat × Nat
  | [] => (0, 0)
  | first :: rest => ((counts first).1 + (countsMany rest).1, (counts first).2 + (countsMany rest).2)
termination_by expressions => sizeOf expressions

/-- Every literal row contributes one edge request after its child construction. -/
def countsRows : List (EdgeSyntax Symbol Guard) → Nat × Nat
  | [] => (0, 0)
  | .mk _ _ children :: rest =>
      ((countsMany children).1 + (countsRows rest).1, 1 + (countsMany children).2 + (countsRows rest).2)
termination_by expressions => sizeOf expressions
end

/-- The static upper bound for node reservations is independent of cache contents. -/
def nodeCount (expression : Syntax Symbol Guard) : Nat := (counts expression).1

/-- The static upper bound for edge reservations is independent of cache contents. -/
def edgeCount (expression : Syntax Symbol Guard) : Nat := (counts expression).2

mutual
/-- Ordinary source syntax constructs a return within its static reservation counts. -/
theorem complete (expression : Syntax Symbol Guard) (domain : SourceNode expression)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    ∃ value after, InternedFreshOrdinaryConstruction.build expression environment state = .done value after ∧
      after.nodes.next ≤ state.nodes.next + (counts expression).1 ∧
      after.edges.next ≤ state.edges.next + (counts expression).2 := by
  cases domain with
  | empty =>
      exact ⟨.empty, state, by simp only [InternedFreshOrdinaryConstruction.build], by simp [counts], by simp [counts]⟩
  | var index =>
      exact ⟨environment[index]?.getD .empty, state,
        by simp only [InternedFreshOrdinaryConstruction.build], by simp [counts], by simp [counts]⟩
  | @ordinary edges domain =>
      obtain ⟨rows, middle, built, nodes, edgesBound⟩ := completeRows edges domain environment state
      let actual := run (makeNode rows) middle
      have one := makeNode_next rows middle
      refine ⟨actual.1, actual.2, ?_, ?_, ?_⟩
      · simp only [InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work, actual]
      · simp only [counts]
        dsimp only [actual]
        omega
      · simp only [counts]
        dsimp only [actual]
        omega
termination_by sizeOf expression

/-- Child construction adds the bounds of the actual ordered syntax occurrences. -/
theorem completeMany (expressions : List (Syntax Symbol Guard)) (domain : SourceChildren expressions)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    ∃ values after, InternedFreshOrdinaryConstruction.buildMany expressions environment state = .done values after ∧
      after.nodes.next ≤ state.nodes.next + (countsMany expressions).1 ∧
      after.edges.next ≤ state.edges.next + (countsMany expressions).2 := by
  cases domain with
  | nil => exact ⟨[], state, by simp only [InternedFreshOrdinaryConstruction.buildMany],
      by simp [countsMany], by simp [countsMany]⟩
  | @cons first rest firstDomain restDomain =>
      obtain ⟨value, middle, built, nodes, edges⟩ := complete first firstDomain environment state
      obtain ⟨values, after, returned, moreNodes, moreEdges⟩ := completeMany rest restDomain environment middle
      refine ⟨value :: values, after, ?_, ?_, ?_⟩
      · simp only [InternedFreshOrdinaryConstruction.buildMany, built, returned, Outcome.bind]
      · simp only [countsMany]; omega
      · simp only [countsMany]; omega
termination_by sizeOf expressions

/-- Row construction adds one edge action to its children and remaining rows. -/
theorem completeRows (expressions : List (EdgeSyntax Symbol Guard)) (domain : SourceRows expressions)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    ∃ values after, InternedFreshOrdinaryConstruction.buildEdges expressions environment state = .done values after ∧
      after.nodes.next ≤ state.nodes.next + (countsRows expressions).1 ∧
      after.edges.next ≤ state.edges.next + (countsRows expressions).2 := by
  cases domain with
  | nil => exact ⟨[], state, by simp only [InternedFreshOrdinaryConstruction.buildEdges],
      by simp [countsRows], by simp [countsRows]⟩
  | @cons children rest symbol guard childrenDomain restDomain =>
      obtain ⟨values, middle, built, nodes, edges⟩ := completeMany children childrenDomain environment state
      let actual := run (makeEdge symbol guard values) middle
      have one := makeEdge_next symbol guard values middle
      obtain ⟨rows, after, returned, moreNodes, moreEdges⟩ := completeRows rest restDomain environment actual.2
      refine ⟨actual.1 :: rows, after, ?_, ?_, ?_⟩
      · dsimp only [actual] at returned ⊢
        simp only [InternedFreshOrdinaryConstruction.buildEdges, built, Outcome.bind, work, returned]
      · simp only [countsRows]
        dsimp only [actual] at moreNodes
        omega
      · simp only [countsRows]
        dsimp only [actual] at moreEdges
        omega
termination_by sizeOf expressions
end

/-- A supplied actual return has the same static counter bounds. -/
theorem build_bounds (expression : Syntax Symbol Guard) (domain : SourceNode expression)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build expression environment state = .done value after) :
    after.nodes.next ≤ state.nodes.next + nodeCount expression ∧
    after.edges.next ≤ state.edges.next + edgeCount expression := by
  obtain ⟨constructed, final, built, nodes, edges⟩ := complete expression domain environment state
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj (built.symm.trans actual)
  exact ⟨nodes, edges⟩

/-- Legitimate resident inputs add domain and record facts at that same constructed return. -/
theorem build (expression : Syntax Symbol Guard) (domain : SourceNode expression)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (domains : Domains environment) :
    ∃ value after, InternedFreshOrdinaryConstruction.build expression environment state = .done value after ∧
      Domain value ∧ Facts after ∧ Available after value ∧
      after.nodes.next ≤ state.nodes.next + nodeCount expression ∧
      after.edges.next ≤ state.edges.next + edgeCount expression := by
  obtain ⟨value, after, built, resultDomain⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryConstruction.build expression domain environment state facts inputs domains
  have verified := InternedFreshOrdinaryFacts.build_verified expression environment state facts inputs
  have finalFacts : Facts after := by simpa only [built, Outcome.state] using verified.facts
  have bounded := build_bounds expression domain environment state value after built
  exact ⟨value, after, built, resultDomain, finalFacts, verified.result value after built, bounded⟩

/-- Closed source construction derives its own return and initial-only absolute resource bounds. -/
theorem closed (expression : Syntax Symbol Guard) (domain : SourceNode expression) :
    ∃ value after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value after ∧
      Domain value ∧ Facts after ∧ Available after value ∧
      after.nodes.next ≤ nodeCount expression ∧ after.edges.next ≤ edgeCount expression := by
  obtain ⟨value, after, actual, resultDomain, facts, available, nodes, edges⟩ :=
    build expression domain [] empty InternedNestedFacts.empty_facts (by intro value member; cases member) .nil
  exact ⟨value, after, actual, resultDomain, facts, available,
    by simpa only [empty, Cache.emptyState, Nat.zero_add] using nodes,
    by simpa only [empty, Cache.emptyState, Nat.zero_add] using edges⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructionReservations
