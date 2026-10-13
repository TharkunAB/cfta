import MicroCFTA.SymbolicHashJoin
import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Ordinary intersection through physical constructor records

This module executes the ordinary-node branch on plain edges. The hash join
uses the source bucket order. Arity mismatch builds the source empty edge.
Child calls run before edge interning. Node interning reads the canonical
surviving records. Recursive, union, and memo dispatch are separate callers.
-/
namespace MicroCFTA.SourceInternedIntersectionRows
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalGroupCalls Language

/-- A record property remains valid after actual constructor effects. -/
def Stable (P : State Symbol Guard → A → Prop) : Prop :=
  ∀ before after, Grows before after → Cache.Extends before.nodes.issued after.nodes.issued →
    ∀ value, P before value → P after value

/-- Available input and result records survive later constructor calls. -/
theorem available_stable : Stable (Available (Symbol := Symbol) (Guard := Guard)) := by
  intro before after growth history value available
  exact available.grows before after growth history

/-- Canonical edge payloads survive later constructor calls. -/
theorem resident_stable : Stable (EdgeResident (Symbol := Symbol) (Guard := Guard)) := by
  intro before after growth _ edge resident
  exact edge_grows before after growth edge resident

/-- Sequential effects preserve every result record and its original position. -/
theorem map_checked [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Work Symbol Guard B) (requests : List A)
    (Input : State Symbol Guard → A → Prop) (Output : State Symbol Guard → B → Prop)
    (relation : A → B → Prop) (inputStable : Stable Input) (outputStable : Stable Output)
    (checked : ∀ request ∈ requests, ∀ state, Facts state → Input state request →
      Facts (run (call request) state).2 ∧ Output (run (call request) state).2 (run (call request) state).1 ∧
        relation request (run (call request) state).1)
    (state : State Symbol Guard) (facts : Facts state) (inputs : ∀ request ∈ requests, Input state request) :
    Facts (run (mapCalls call requests) state).2 ∧
      (∀ value ∈ (run (mapCalls call requests) state).1, Output (run (mapCalls call requests) state).2 value) ∧
      All₂ relation requests (run (mapCalls call requests) state).1 := by
  induction requests generalizing state with
  | nil => exact ⟨facts, by simp [mapCalls, run], .nil⟩
  | cons request rest ih =>
      have head := checked request List.mem_cons_self state facts (inputs request List.mem_cons_self)
      have growth := (InternedConstructorTemplates.run_correct (call request) state facts.coherent.valid).2
      have history := run_issued_extends (call request) state facts.coherent.valid
      have tail := ih (fun item member => checked item (List.mem_cons_of_mem _ member))
        (run (call request) state).2 head.1
        (fun item member => inputStable state _ growth history item (inputs item (List.mem_cons_of_mem _ member)))
      have tailGrowth := (InternedConstructorTemplates.run_correct (mapCalls call rest)
        (run (call request) state).2 head.1.coherent.valid).2
      have tailHistory := run_issued_extends (mapCalls call rest)
        (run (call request) state).2 head.1.coherent.valid
      simp only [mapCalls, run_bind, run]
      refine ⟨tail.1, ?_, .cons head.2.2 tail.2.2⟩
      intro value member
      rcases List.mem_cons.mp member with rfl | later
      · exact outputStable _ _ tailGrowth tailHistory _ head.2.1
      · exact tail.2.1 value later

/-- Both operands of one child call are complete available records. -/
def Inputs (state : State Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) : Prop :=
  Available state pair.1 ∧ Available state pair.2

/-- Earlier operand pairs remain usable during later child calls. -/
theorem inputs_stable : Stable (Inputs (Symbol := Symbol) (Guard := Guard)) := by
  intro before after growth history pair inputs
  exact ⟨inputs.1.grows before after growth history, inputs.2.grows before after growth history⟩

/-- Both input rows are stored complete edge payloads. -/
def EdgeInputs (state : State Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) : Prop :=
  EdgeResident state pair.1 ∧ EdgeResident state pair.2

/-- Earlier row operands remain resident during later row calls. -/
theorem edgeInputs_stable : Stable (EdgeInputs (Symbol := Symbol) (Guard := Guard)) := by
  intro before after growth _ pair inputs
  exact ⟨edge_grows before after growth _ inputs.1, edge_grows before after growth _ inputs.2⟩

/-- The source ordinary-edge branch checks arity before it evaluates children. -/
def edge (call : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (pair : EdgeValue Symbol Unit × EdgeValue Symbol Unit) : Work Symbol Unit (EdgeValue Symbol Unit) :=
  if pair.1.children.length = pair.2.children.length then
    (mapCalls call (pair.1.children.zip pair.2.children)).bind fun values =>
      makeEdge pair.1.entry.key.symbol () values
  else makeEdge pair.1.entry.key.symbol () [.empty]

/-- Source hash-join occurrences retain the reversed right bucket order. -/
def pairs [DecidableEq Symbol] (left right : List (EdgeValue Symbol Unit)) :=
  SymbolicHashJoin.hashJoin (fun row : EdgeValue Symbol Unit => row.entry.key.symbol) Prod.mk left right

/-- The ordinary node evaluates each matched row before node normalization. -/
def node [DecidableEq Symbol]
    (call : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (left right : List (EdgeValue Symbol Unit)) : Work Symbol Unit (Value Symbol Unit) :=
  (mapCalls (edge call) (pairs left right)).bind makeNode

/-- The source buckets emit exactly the equal-symbol row pairs. -/
theorem pairs_member [DecidableEq Symbol] (left right : List (EdgeValue Symbol Unit)) (pair) :
    pair ∈ pairs left right ↔ pair.1 ∈ left ∧ pair.2 ∈ right ∧ pair.1.entry.key.symbol = pair.2.entry.key.symbol := by
  rw [pairs, SymbolicHashJoin.hashJoin_member]
  constructor
  · rintro ⟨first, firstIn, second, secondIn, same, rfl⟩
    exact ⟨firstIn, secondIn, same⟩
  · rintro ⟨firstIn, secondIn, same⟩
    exact ⟨pair.1, firstIn, pair.2, secondIn, same, rfl⟩

/-- The stored edge retains the actual ordered child results, including on a cache hit. -/
theorem edge_checked [DecidableEq Symbol]
    (call : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (pair : EdgeValue Symbol Unit × EdgeValue Symbol Unit)
    (relation : (Value Symbol Unit × Value Symbol Unit) → Value Symbol Unit → Prop)
    (checked : ∀ request ∈ pair.1.children.zip pair.2.children, ∀ state, Facts state → Inputs state request →
      Facts (run (call request) state).2 ∧ Available (run (call request) state).2 (run (call request) state).1 ∧
        relation request (run (call request) state).1)
    (state : State Symbol Unit) (facts : Facts state) (inputs : EdgeInputs state pair) :
    let result := run (edge call pair) state
    Facts result.2 ∧ EdgeResident result.2 result.1 ∧ result.1.entry.key.symbol = pair.1.entry.key.symbol ∧
      result.1.entry.key.constraint = () ∧
      (if pair.1.children.length = pair.2.children.length then
        All₂ relation (pair.1.children.zip pair.2.children) result.1.children
       else result.1.children = [.empty]) := by
  by_cases arity : pair.1.children.length = pair.2.children.length
  · have inputsChildren : ∀ request ∈ pair.1.children.zip pair.2.children, Inputs state request := by
      intro request member
      have positions := List.of_mem_zip member
      exact ⟨facts.cached.edges _ _ inputs.1 _ positions.1, facts.cached.edges _ _ inputs.2 _ positions.2⟩
    have children := map_checked call _ Inputs Available relation inputs_stable available_stable checked state facts inputsChildren
    have built := edge_verified pair.1.entry.key.symbol () _ _ children.1 children.2.1
    have fields := MergedPhysicalGroupEdges.makeEdge_fields _ children.1 pair.1.entry.key.symbol () _ children.2.1
    simp only [edge, arity, ↓reduceIte, run_bind]
    exact ⟨built.facts, built.result _ _ rfl, fields.1, trivial, by rw [fields.2.2]; exact children.2.2⟩
  · have available : Values state [.empty] := by
      intro value member
      rw [List.mem_singleton.mp member]
      exact empty_available state
    have built := edge_verified pair.1.entry.key.symbol () [.empty] state facts available
    have fields := MergedPhysicalGroupEdges.makeEdge_fields state facts pair.1.entry.key.symbol () [.empty] available
    simp only [edge, arity, ↓reduceIte]
    exact ⟨built.facts, built.result _ _ rfl, fields.1, trivial, fields.2.2⟩

/-- Completed row calls expose exactly the canonical surviving physical rows. -/
theorem node_readback [DecidableEq Symbol]
    (call : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (left right : List (EdgeValue Symbol Unit)) (state : State Symbol Unit)
    (facts : Facts (run (mapCalls (edge call) (pairs left right)) state).2)
    (resident : Edges (run (mapCalls (edge call) (pairs left right)) state).2
      (run (mapCalls (edge call) (pairs left right)) state).1) :
    nodeEdges (run (node call left right) state).1 =
      canonicalEdges (surviving (run (mapCalls (edge call) (pairs left right)) state).1) := by
  simp only [node, run_bind]
  exact EqualityLeafProjectionPhysical.makeNode_edges _ _ facts.coherent facts.linked resident

/-- The complete physical branch derives exact stored-row membership from child provenance alone. -/
theorem node_rows_checked [DecidableEq Symbol]
    (call : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (left right : List (EdgeValue Symbol Unit))
    (checked : ∀ pair ∈ pairs left right, ∀ request ∈ pair.1.children.zip pair.2.children,
      ∀ state, Facts state → Inputs state request →
        Facts (run (call request) state).2 ∧ Available (run (call request) state).2 (run (call request) state).1)
    (state : State Symbol Unit) (facts : Facts state) (leftResident : Edges state left) (rightResident : Edges state right) :
    let built := run (mapCalls (edge call) (pairs left right)) state
    let result := run (node call left right) state
    Facts result.2 ∧ Available result.2 result.1 ∧
      nodeEdges result.1 = canonicalEdges (surviving built.1) ∧
      ∀ row, row ∈ nodeEdges result.1 ↔ row ∈ built.1 ∧ EqualityLeafProjectionPhysical.dead row = false := by
  have edgesChecked : ∀ pair ∈ pairs left right, ∀ state, Facts state → EdgeInputs state pair →
      Facts (run (edge call pair) state).2 ∧ EdgeResident (run (edge call pair) state).2 (run (edge call pair) state).1 ∧ True := by
    intro pair member state facts inputs
    have result := edge_checked call pair (fun _ _ => True)
      (fun request included next nextFacts nextInputs =>
        let child := checked pair member request included next nextFacts nextInputs
        ⟨child.1, child.2, trivial⟩) state facts inputs
    exact ⟨result.1, result.2.1, trivial⟩
  have inputs : ∀ pair ∈ pairs left right, EdgeInputs state pair := by
    intro pair member
    have original := (pairs_member left right pair).mp member
    exact ⟨leftResident pair.1 original.1, rightResident pair.2 original.2.1⟩
  have built := map_checked (edge call) (pairs left right) EdgeInputs EdgeResident (fun _ _ => True)
    edgeInputs_stable resident_stable edgesChecked state facts inputs
  have result := node_verified _ _ built.1 built.2.1
  have rows := node_readback call left right state built.1 built.2.1
  refine ⟨?_, ?_, rows, ?_⟩
  · simp only [node, run_bind]
    exact result.facts
  · simp only [node, run_bind]
    exact result.result _ _ rfl
  · intro row
    rw [rows]
    exact EqualityLeafProjectionPhysical.normalized_member _ built.1.coherent _ built.2.1 row

end MicroCFTA.SourceInternedIntersectionRows
