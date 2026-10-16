import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
import MicroCFTA.InternedFreshOrdinaryFacts

/-!
# Finite ordinary source construction

The source domain contains Empty, lexical variables, and ordinary nodes.
Available domain environments retain every selected variable value.
The actual constructor computes its own completed value and domain.
No successful construction or final domain is an input premise.
Mu and union construction remain outside this intermediate domain.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstruction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedFacts (Facts)
open InternedNestedProvenance (Values Edges)
open InternedFreshOrdinaryConstruction
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

mutual
/-- Source nodes use ordinary constructors and their ordered child syntax. -/
inductive Node : Syntax Symbol Guard → Prop where
  | empty : Node .empty
  | var (index : Nat) : Node (.var index)
  | ordinary (rows : Rows edges) : Node (.node edges)

/-- Source children retain the domain at each literal position. -/
inductive Children : List (Syntax Symbol Guard) → Prop where
  | nil : Children []
  | cons (first : Node value) (rest : Children values) : Children (value :: values)

/-- Source rows permit arbitrary symbols and full guards. -/
inductive Rows : List (EdgeSyntax Symbol Guard) → Prop where
  | nil : Rows []
  | cons (children : Children values) (rest : Rows edges) : Rows (.mk symbol constraint values :: edges)
end

mutual
/-- Ordinary source syntax constructs its own completed domain value. -/
theorem build (expression : Syntax Symbol Guard) (domain : Node expression)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (domains : DChildren environment) :
    ∃ value after, InternedFreshOrdinaryConstruction.build expression environment state = .done value after ∧ DNode value := by
  cases domain with
  | empty => exact ⟨.empty, state, by simp only [InternedFreshOrdinaryConstruction.build], .empty⟩
  | var index =>
      cases found : environment[index]? with
      | none => exact ⟨.empty, state, by simp only [InternedFreshOrdinaryConstruction.build, found, Option.getD_none], .empty⟩
      | some value => exact ⟨value, state,
          by simp only [InternedFreshOrdinaryConstruction.build, found, Option.getD_some],
          domains.member value (List.mem_of_getElem? found)⟩
  | @ordinary edges rows =>
      obtain ⟨values, middle, returned, resultDomain⟩ := buildEdges edges rows environment state facts inputs domains
      have verified := InternedFreshOrdinaryFacts.buildEdges_verified edges environment state facts inputs
      have current : Facts middle := by simpa only [returned, InternedNestedConstruction.Outcome.state] using verified.facts
      have resident := verified.result values middle returned
      exact ⟨_, (run (makeNode values) middle).2, by simp only [InternedFreshOrdinaryConstruction.build, returned, Outcome.bind, work],
        SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode values middle current.coherent current.linked resident resultDomain⟩
termination_by sizeOf expression

/-- Ordered source child construction returns a domain forest at its actual final heap. -/
theorem buildMany (expressions : List (Syntax Symbol Guard)) (domain : Children expressions)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (domains : DChildren environment) :
    ∃ values after, InternedFreshOrdinaryConstruction.buildMany expressions environment state = .done values after ∧ DChildren values := by
  cases domain with
  | nil => exact ⟨[], state, by simp only [InternedFreshOrdinaryConstruction.buildMany], .nil⟩
  | @cons first rest firstDomain restDomain =>
      obtain ⟨value, middle, returned, resultDomain⟩ := build first firstDomain environment state facts inputs domains
      have verified := InternedFreshOrdinaryFacts.build_verified first environment state facts inputs
      have current : Facts middle := by simpa only [returned, InternedNestedConstruction.Outcome.state] using verified.facts
      have nextInputs : Values middle environment := fun item member => by
        simpa only [returned, InternedNestedConstruction.Outcome.state] using verified.available item (inputs item member)
      obtain ⟨values, after, tailReturned, tailDomains⟩ := buildMany rest restDomain environment middle current nextInputs domains
      exact ⟨value :: values, after,
        by simp only [InternedFreshOrdinaryConstruction.buildMany, returned, tailReturned, Outcome.bind],
        .cons resultDomain tailDomains⟩
termination_by sizeOf expressions

/-- Ordered source rows construct their own complete edge records and child domains. -/
theorem buildEdges (expressions : List (EdgeSyntax Symbol Guard)) (domain : Rows expressions)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (domains : DChildren environment) :
    ∃ values after, InternedFreshOrdinaryConstruction.buildEdges expressions environment state = .done values after ∧ DRows values := by
  cases domain with
  | nil => exact ⟨[], state, by simp only [InternedFreshOrdinaryConstruction.buildEdges], .nil⟩
  | @cons children rest symbol constraint childrenDomain restDomain =>
      obtain ⟨values, middle, returned, resultDomain⟩ := buildMany children childrenDomain environment state facts inputs domains
      have verified := InternedFreshOrdinaryFacts.buildMany_verified children environment state facts inputs
      have current : Facts middle := by simpa only [returned, InternedNestedConstruction.Outcome.state] using verified.facts
      have available := verified.result values middle returned
      let made := run (makeEdge symbol constraint values) middle
      have edgeVerified := InternedNestedFacts.edge_verified symbol constraint values middle current available
      have edgeFacts : Facts made.2 := edgeVerified.facts
      have nextInputs : Values made.2 environment := fun item member => by
        apply edgeVerified.available item
        simpa only [returned, InternedNestedConstruction.Outcome.state] using verified.available item (inputs item member)
      have edgeDomain := SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge symbol constraint values middle
        current.coherent current.cached available resultDomain
      obtain ⟨edges, after, tailReturned, tailDomains⟩ := buildEdges rest restDomain environment made.2 edgeFacts nextInputs domains
      dsimp only [made] at tailReturned
      exact ⟨made.1 :: edges, after,
        by simp only [InternedFreshOrdinaryConstruction.buildEdges, returned, Outcome.bind, work, tailReturned, made],
        .cons edgeDomain tailDomains⟩
termination_by sizeOf expressions
end

/-- Closed ordinary source syntax derives success, domain, and resident record facts from the empty heap. -/
theorem closed (expression : Syntax Symbol Guard) (domain : Node expression) :
    ∃ value after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value after ∧
      DNode value ∧ Facts after ∧ Available after value := by
  obtain ⟨value, after, returned, resultDomain⟩ := build expression domain [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member) .nil
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  exact ⟨value, after, returned, resultDomain,
    by simpa only [returned, InternedNestedConstruction.Outcome.state] using verified.facts,
    verified.result value after returned⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstruction
