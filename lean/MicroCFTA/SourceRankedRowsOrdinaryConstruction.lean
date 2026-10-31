import MicroCFTA.SourceSizedDecided
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain

/-!
# Ordinary construction from original ranked rows

This module unfolds a ranked DAG in the original row and child order.
It uses the actual fresh source executor and ordinary native constructors.
It does not model SCC extraction, source memo hits or their allocation order.
-/
namespace MicroCFTA.SourceRankedRowsOrdinaryConstruction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open InternedNestedFacts (Facts)
open SourceSizedDecided (Row)
variable {Q Symbol Guard : Type}

/-- Copy each original row with its label, constraint and ordered children. -/
def layer (source : List (Row Q Symbol Guard)) (child : Q → Syntax Symbol Guard) :
    List (EdgeSyntax Symbol Guard) :=
  source.map fun row => .mk row.label row.constraint (row.children.map child)

/-- Unfold only ordinary constructors, without a binder or union wrapper. -/
def expression (source : Q → List (Row Q Symbol Guard)) : Nat → Q → Syntax Symbol Guard
  | 0, _ => .empty
  | fuel + 1, current => .node (layer (source current) (expression source fuel))

/-- One layer retains the exact original row sequence and child sequence. -/
theorem expression_succ (source : Q → List (Row Q Symbol Guard)) (fuel : Nat) (current : Q) :
    expression source (fuel + 1) current =
      .node ((source current).map fun row =>
        .mk row.label row.constraint (row.children.map (expression source fuel))) := rfl

/-- Sufficient original rank makes the expression independent of extra unfolding fuel. -/
theorem expression_stable (source : Q → List (Row Q Symbol Guard)) (rank : Q → Nat)
    (decreases : ∀ current row, row ∈ source current → ∀ child ∈ row.children, rank child < rank current)
    (leftFuel rightFuel : Nat) (current : Q)
    (left : rank current < leftFuel) (right : rank current < rightFuel) :
    expression source leftFuel current = expression source rightFuel current := by
  induction leftFuel generalizing rightFuel current with
  | zero => omega
  | succ fuel ih =>
      cases rightFuel with
      | zero => omega
      | succ later =>
          rw [expression_succ, expression_succ]
          apply congrArg Syntax.node
          apply List.map_congr_left
          intro row member
          apply congrArg (fun children => EdgeSyntax.mk row.label row.constraint children)
          apply List.map_congr_left
          intro child listed
          have smaller := decreases current row member child listed
          exact ih later child (by omega) (by omega)

variable [DecidableEq (EdgeKey Symbol Guard)]

mutual
private theorem build_node_domain
    (source : Q → List (Row Q Symbol Guard)) (rank : Q → Nat)
    (positive : ∀ current row, row ∈ source current → 0 < rank current)
    (decreases : ∀ current row, row ∈ source current → ∀ child ∈ row.children, rank child < rank current)
    (fuel : Nat) (current : Q) (within : rank current < fuel)
    (state : State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (observed : build (expression source fuel current) [] state = .done value after) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧
      MergedOrdinaryHeight.height value ≤ rank current := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      simp only [expression, build] at observed
      change ((buildEdges (layer (source current) (expression source fuel)) [] state).bind
        fun edges middle => work (makeNode edges) middle) = .done value after at observed
      cases edgesObserved : buildEdges (layer (source current) (expression source fuel)) [] state with
      | pending key middle => simp [edgesObserved, Outcome.bind] at observed
      | done edges middle =>
          have domain := build_rows_domain source rank positive decreases fuel (source current) (rank current)
            (fun row member => positive current row member)
            (by intro row member child listed; have step := decreases current row member child listed; omega)
            (fun row member child listed => decreases current row member child listed)
            state facts edges middle edgesObserved
          have checked := InternedFreshOrdinaryFacts.buildEdges_verified
            (layer (source current) (expression source fuel)) [] state facts (by intro item member; cases member)
          have middleFacts : Facts middle := by
            simpa only [edgesObserved, Outcome.state] using checked.facts
          have resident : ∀ edge ∈ edges, EdgeResident middle edge := checked.result edges middle edgesObserved
          have nodeDomain := SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode
            edges middle middleFacts.coherent middleFacts.linked resident domain.1
          have nodeBound := SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound
            edges middle middleFacts.coherent middleFacts.linked resident (rank current) domain.2
          simp only [edgesObserved, Outcome.bind, work, Outcome.done.injEq] at observed
          exact observed.1 ▸ ⟨nodeDomain, nodeBound⟩
termination_by (fuel, 0, 0)
decreasing_by
  all_goals
    simp_wf
    exact Prod.Lex.left _ _ (by omega)

private theorem build_many_domain
    (source : Q → List (Row Q Symbol Guard)) (rank : Q → Nat)
    (positive : ∀ current row, row ∈ source current → 0 < rank current)
    (decreases : ∀ current row, row ∈ source current → ∀ child ∈ row.children, rank child < rank current)
    (fuel : Nat) (states : List Q) (within : ∀ current ∈ states, rank current < fuel)
    (bound : Nat) (bounded : ∀ current ∈ states, rank current ≤ bound)
    (state : State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (observed : buildMany (states.map (expression source fuel)) [] state = .done values after) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Children values ∧
      ∀ value ∈ values, MergedOrdinaryHeight.height value ≤ bound := by
  cases states with
  | nil =>
      simp only [List.map_nil, buildMany, Outcome.done.injEq] at observed
      rcases observed with ⟨rfl, rfl⟩
      exact ⟨.nil, by intro value member; cases member⟩
  | cons current rest =>
      simp only [List.map_cons, buildMany] at observed
      change ((build (expression source fuel current) [] state).bind fun value middle =>
        (buildMany (rest.map (expression source fuel)) [] middle).bind
          fun values final => .done (value :: values) final) = .done values after at observed
      cases headObserved : build (expression source fuel current) [] state with
      | pending key middle => simp [headObserved, Outcome.bind] at observed
      | done value middle =>
          have head := build_node_domain source rank positive decreases fuel current
            (within current List.mem_cons_self) state facts value middle headObserved
          have checked := InternedFreshOrdinaryFacts.build_verified
            (expression source fuel current) [] state facts (by intro item member; cases member)
          have middleFacts : Facts middle := by
            simpa only [headObserved, Outcome.state] using checked.facts
          cases tailObserved : buildMany (rest.map (expression source fuel)) [] middle with
          | pending key final => simp [headObserved, Outcome.bind, tailObserved] at observed
          | done tail final =>
              have later := build_many_domain source rank positive decreases fuel rest
                (fun item member => within item (List.mem_cons_of_mem _ member)) bound
                (fun item member => bounded item (List.mem_cons_of_mem _ member))
                middle middleFacts tail final tailObserved
              have result : SourceCurrentAllocatedFiniteOrdinaryDomain.Children (value :: tail) ∧
                  ∀ item ∈ value :: tail, MergedOrdinaryHeight.height item ≤ bound := by
                refine ⟨.cons head.1 later.1, ?_⟩
                intro item member
                rcases List.mem_cons.mp member with rfl | listed
                · exact Nat.le_trans head.2 (bounded current List.mem_cons_self)
                · exact later.2 item listed
              simp only [headObserved, Outcome.bind, tailObserved, Outcome.done.injEq] at observed
              exact observed.1 ▸ result
termination_by (fuel, 1, states.length)
decreasing_by
  all_goals
    simp_wf
    first
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
    | apply Prod.Lex.right _
      apply Prod.Lex.right _
      rw [show states = current :: rest from by assumption]
      exact Nat.lt_succ_self _

private theorem build_rows_domain
    (source : Q → List (Row Q Symbol Guard)) (rank : Q → Nat)
    (positive : ∀ current row, row ∈ source current → 0 < rank current)
    (decreases : ∀ current row, row ∈ source current → ∀ child ∈ row.children, rank child < rank current)
    (fuel : Nat) (rows : List (Row Q Symbol Guard)) (bound : Nat)
    (rowPositive : ∀ row ∈ rows, 0 < bound)
    (within : ∀ row ∈ rows, ∀ child ∈ row.children, rank child < fuel)
    (bounded : ∀ row ∈ rows, ∀ child ∈ row.children, rank child < bound)
    (state : State Symbol Guard) (facts : Facts state)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (observed : buildEdges (layer rows (expression source fuel)) [] state = .done edges after) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Rows edges ∧
      ∀ edge ∈ edges, MergedOrdinaryHeight.edgeHeight edge + 1 ≤ bound := by
  cases rows with
  | nil =>
      simp only [layer, List.map_nil, buildEdges, Outcome.done.injEq] at observed
      rcases observed with ⟨rfl, rfl⟩
      exact ⟨.nil, by intro edge member; cases member⟩
  | cons row rest =>
      simp only [layer, List.map_cons, buildEdges] at observed
      change ((buildMany (row.children.map (expression source fuel)) [] state).bind fun children middle =>
        (work (makeEdge row.label row.constraint children) middle).bind fun edge afterEdge =>
          (buildEdges (layer rest (expression source fuel)) [] afterEdge).bind
            fun edges final => .done (edge :: edges) final) = .done edges after at observed
      cases childrenObserved : buildMany (row.children.map (expression source fuel)) [] state with
      | pending key middle => simp [childrenObserved, Outcome.bind] at observed
      | done children middle =>
          have childDomains := build_many_domain source rank positive decreases fuel row.children
            (fun child listed => within row List.mem_cons_self child listed) (bound - 1)
            (by intro child listed; have smaller := bounded row List.mem_cons_self child listed; omega)
            state facts children middle childrenObserved
          have checked := InternedFreshOrdinaryFacts.buildMany_verified
            (row.children.map (expression source fuel)) [] state facts (by intro item member; cases member)
          have middleFacts : Facts middle := by
            simpa only [childrenObserved, Outcome.state] using checked.facts
          have available : ∀ value ∈ children, Available middle value := checked.result children middle childrenObserved
          let edgeResult := run (makeEdge row.label row.constraint children) middle
          have edgeDomain := SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge
            row.label row.constraint children middle middleFacts.coherent middleFacts.cached available childDomains.1
          have edgeBound := SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound
            row.label row.constraint children middle middleFacts.coherent middleFacts.cached available
            (bound - 1) childDomains.2
          have edgeChecked := InternedNestedFacts.edge_verified row.label row.constraint children middle middleFacts available
          have edgeFacts : Facts edgeResult.2 := by
            simpa only [work, Outcome.state] using edgeChecked.facts
          cases tailObserved : buildEdges (layer rest (expression source fuel)) [] edgeResult.2 with
          | pending key final => simp [childrenObserved, Outcome.bind, work, tailObserved, edgeResult] at observed
          | done tail final =>
              dsimp only [edgeResult] at tailObserved
              have later := build_rows_domain source rank positive decreases fuel rest bound
                (fun item member => rowPositive item (List.mem_cons_of_mem _ member))
                (fun item member child listed => within item (List.mem_cons_of_mem _ member) child listed)
                (fun item member child listed => bounded item (List.mem_cons_of_mem _ member) child listed)
                edgeResult.2 edgeFacts tail final tailObserved
              have result : SourceCurrentAllocatedFiniteOrdinaryDomain.Rows (edgeResult.1 :: tail) ∧
                  ∀ edge ∈ edgeResult.1 :: tail, MergedOrdinaryHeight.edgeHeight edge + 1 ≤ bound := by
                refine ⟨.cons edgeDomain later.1, ?_⟩
                intro edge member
                rcases List.mem_cons.mp member with rfl | listed
                · have strictlyPositive := rowPositive row List.mem_cons_self
                  change MergedOrdinaryHeight.edgeHeight (run (makeEdge row.label row.constraint children) middle).1 + 1 ≤ bound
                  omega
                · exact later.2 edge listed
              simp only [childrenObserved, Outcome.bind, work, tailObserved, Outcome.done.injEq] at observed
              exact observed.1 ▸ result
termination_by (fuel, 2, rows.length)
decreasing_by
  all_goals
    simp_wf
    first
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
    | apply Prod.Lex.right _
      apply Prod.Lex.right _
      rw [show rows = row :: rest from by assumption]
      exact Nat.lt_succ_self _
end

/-- Original positive row ranks produce the complete ordinary native value. -/
theorem closed
    (source : Q → List (Row Q Symbol Guard)) (rank : Q → Nat)
    (positive : ∀ current row, row ∈ source current → 0 < rank current)
    (decreases : ∀ current row, row ∈ source current → ∀ child ∈ row.children, rank child < rank current)
    (root : Q) :
    ∃ (value : Value Symbol Guard) (heap : State Symbol Guard),
      build (expression source (rank root + 1) root) [] empty = .done value heap ∧
      Facts heap ∧ Available heap value ∧ value.free = [] ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧
      MergedOrdinaryHeight.height value ≤ rank root := by
  obtain ⟨value, heap, observed⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete
    (expression source (rank root + 1) root)
  have checked := InternedFreshOrdinaryFacts.closed_verified (expression source (rank root + 1) root)
  have facts : Facts heap := by simpa only [observed, Outcome.state] using checked.facts
  have available := checked.result value heap observed
  have free := InternedFreshOrdinarySourceFreeNames.closed_free_empty
    (expression source (rank root + 1) root) value heap observed
  have domain := build_node_domain source rank positive decreases (rank root + 1) root
    (Nat.lt_succ_self _) empty InternedNestedFacts.empty_facts value heap observed
  exact ⟨value, heap, observed, facts, available, free, domain.1, domain.2⟩

end MicroCFTA.SourceRankedRowsOrdinaryConstruction
