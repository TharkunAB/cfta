import MicroCFTA.EqualityLeafProjectionCompileAvailability

/-!
# Derived finite ordinary inputs for recursive path workers

Original occurrence compilation produces finite ordinary records when its
leaf constructor does. Exact child payload readback carries this invariant
through edge cache hits. Worker completion therefore follows from the
compiled representation, rather than a separate physical-input premise.
-/
namespace MicroCFTA.EqualityLeafProjectionCompileOrdinary
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (Tree Edge)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionWorkers

/-- Local leaf construction stays inside the finite ordinary source fragment. -/
def LeafOrdinary [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value state, Facts state → Ordinary (run (leaf value) state).1

mutual
/-- Actual occurrence compilation produces a finite ordinary source value. -/
theorem compile_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (available : LeafAvailable leaf) (ordinary : LeafOrdinary leaf)
    (tree : Tree (Tag Symbol Guard) Leaf) (state : State Symbol Guard) (facts : Facts state) :
    Ordinary (run (EqualityLeafProjectionCompile.compile leaf tree) state).1 := by
  cases tree with
  | empty => trivial
  | leaf value => exact ordinary value state facts
  | node edges =>
      let rows := run (EqualityLeafProjectionCompile.compileEdges leaf edges) state
      have rowsFacts := compileEdges_available leaf available edges state facts
      have rowsOrdinary := compileEdges_ordinary leaf available ordinary edges state facts
      have children := EqualityLeafProjectionParentStep.normalized_ordinary rows.1 rows.2 rowsFacts.1.coherent
        rowsFacts.1.linked (fun edge member => (rowsFacts.2 edge member).1) rowsOrdinary
      have root := EqualityLeafProjectionUnion.makeNode_ordinary rows.1 rows.2 rowsFacts.1.coherent
        rowsFacts.1.linked (fun edge member => (rowsFacts.2 edge member).1)
      simp only [EqualityLeafProjectionCompile.compile, run_bind]
      change Ordinary (run (makeNode rows.1) rows.2).1
      cases shape : (run (makeNode rows.1) rows.2).1 with
      | empty => trivial
      | node => simpa only [shape, nodeEdges, EqualityLeafProjectionWorkers.Ordinary] using children
      | reference | union | mu => simp only [shape, EqualityLeafProjectionUnion.OrdinaryRoot] at root
termination_by sizeOf tree

/-- Exact physical edge children retain the finite ordinary occurrence invariant. -/
theorem compileEdges_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (available : LeafAvailable leaf) (ordinary : LeafOrdinary leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (facts : Facts state) :
    ∀ edge ∈ (run (EqualityLeafProjectionCompile.compileEdges leaf edges) state).1,
      ∀ child ∈ edge.children, Ordinary child := by
  cases edges with
  | nil => simp [EqualityLeafProjectionCompile.compileEdges, run]
  | cons edge rest =>
      cases edge with
      | mk tag children =>
          let childResult := run (EqualityLeafProjectionCompile.compileForest leaf children) state
          have childFacts := compileForest_available leaf available children state facts
          have childOrdinary := compileForest_ordinary leaf available ordinary children state facts
          let edgeResult := run (makeEdge tag.1 tag.2 childResult.1) childResult.2
          have edgeAvailable := makeEdge_available tag.1 tag.2 childResult.1 childResult.2
            childFacts.1.coherent childFacts.1.cached childFacts.2
          have edgeLinked := makeEdge_linked tag.1 tag.2 childResult.1 childResult.2 childFacts.1.coherent childFacts.1.linked
          have edgeFacts : Facts edgeResult.2 := ⟨edgeAvailable.1, edgeAvailable.2.1, edgeLinked.1⟩
          have exactChildren := edge_children leaf available children tag state facts
          have tailOrdinary := compileEdges_ordinary leaf available ordinary rest edgeResult.2 edgeFacts
          intro selected member child present
          simp only [EqualityLeafProjectionCompile.compileEdges, run_bind, run, List.mem_cons] at member
          rcases member with same | tail
          · subst selected
            rw [exactChildren] at present
            exact childOrdinary child present
          · exact tailOrdinary selected tail child present
termination_by sizeOf edges

/-- Every compiled ordered child remains an ordinary value after later siblings. -/
theorem compileForest_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (available : LeafAvailable leaf) (ordinary : LeafOrdinary leaf)
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (facts : Facts state) :
    ∀ value ∈ (run (EqualityLeafProjectionCompile.compileForest leaf forest) state).1, Ordinary value := by
  cases forest with
  | nil => simp [EqualityLeafProjectionCompile.compileForest, run]
  | cons first rest =>
      let head := run (EqualityLeafProjectionCompile.compile leaf first) state
      have headFacts := compile_available leaf available first state facts
      have headOrdinary := compile_ordinary leaf available ordinary first state facts
      have tailOrdinary := compileForest_ordinary leaf available ordinary rest head.2 headFacts.1
      intro value member
      simp only [EqualityLeafProjectionCompile.compileForest, run_bind, run, List.mem_cons] at member
      rcases member with same | tail
      · subst value
        exact headOrdinary
      · exact tailOrdinary value tail
termination_by sizeOf forest
end

/-- Canonical nullary construction derives the finite ordinary leaf invariant. -/
theorem nullary_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (Symbol × Guard)) (state : State Symbol Guard) (facts : Facts state) :
    Ordinary (run (EqualityLeafProjectionNullary.build rows) state).1 := by
  have root := (EqualityLeafProjectionUnion.nullary_shape rows state facts.coherent facts.linked).1
  have children := EqualityLeafProjectionLeafWorkers.nullary_children rows state facts.coherent facts.linked
  have ordinary := EqualityLeafProjectionParentStep.ordinary_edges
    (nodeEdges (run (EqualityLeafProjectionNullary.build rows) state).1) (by
      intro edge member child present
      rw [children edge member] at present
      cases present)
  cases shape : (run (EqualityLeafProjectionNullary.build rows) state).1 with
  | empty => trivial
  | node => simpa only [shape, nodeEdges, EqualityLeafProjectionWorkers.Ordinary] using ordinary
  | reference | union | mu => simp only [shape, EqualityLeafProjectionUnion.OrdinaryRoot] at root

noncomputable local instance : DecidableEq EqualityLeafProjectionLeafCache.ConstraintKey := by classical exact inferInstance

/-- The admitted leaf implementation discharges the local ordinary-input requirement. -/
theorem admitted_ordinary : LeafOrdinary (EqualityLeafProjectionLeafCache.build (initial := initial) (symbols := symbols)) := by
  intro value state facts
  rw [EqualityLeafProjectionProduct.leaf_build]
  exact nullary_ordinary _ state facts

/-- Every compiled admitted occurrence is an actual completing input of both physical path workers. -/
theorem admitted_workers
    (tree : Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityLeafProjectionLeafCache.Leaf initial symbols))
    (state current : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (facts : Facts state)
    (meet : Target → Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey →
      Work (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey (Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey))
    (edits : List (EqualityLeafProjectionSyntax.Path × Target)) (paths : List EqualityLeafProjectionSyntax.Path) :
    let value := (run (EqualityLeafProjectionCompile.compile EqualityLeafProjectionLeafCache.build tree) state).1
    Returns (edit meet edits value) current ∧ Returns (require paths value) current := by
  have ordinary := compile_ordinary EqualityLeafProjectionLeafCache.build admitted_leaves admitted_ordinary tree state facts
  exact ⟨edit_returns meet edits _ ordinary current, require_returns paths _ ordinary current⟩

end MicroCFTA.EqualityLeafProjectionCompileOrdinary
