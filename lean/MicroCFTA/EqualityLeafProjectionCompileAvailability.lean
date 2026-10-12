import MicroCFTA.EqualityLeafProjectionParentStep
import MicroCFTA.InternedShallowValues

/-!
# Available records from finite occurrence compilation

A compiled occurrence retains complete available child records and links
every stored node edge to its canonical payload. The proof follows actual
cache effects. This supplies the payload premises for recursive source
correspondence, beyond equality of child reference keys.
-/
namespace MicroCFTA.EqualityLeafProjectionCompileAvailability
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (Tree Edge)
open EqualityLeafProjectionCompile (Tag)

/-- The finite compiler needs complete coherent node, edge, and child payloads. -/
structure Facts (state : State Symbol Guard) : Prop where
  coherent : Coherent state
  cached : Cached state
  linked : Linked state

/-- A leaf constructor establishes the same payload invariants as ancestor construction. -/
def LeafAvailable [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value state, Facts state → Facts (run (leaf value) state).2 ∧ Available (run (leaf value) state).2 (run (leaf value) state).1

mutual
/-- Actual occurrence compilation derives complete output availability. -/
theorem compile_available [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (tree : Tree (Tag Symbol Guard) Leaf) (state : State Symbol Guard) (facts : Facts state) :
    let result := run (EqualityLeafProjectionCompile.compile leaf tree) state
    Facts result.2 ∧ Available result.2 result.1 := by
  cases tree with
  | empty => exact ⟨facts, empty_available state⟩
  | leaf value => exact leaves value state facts
  | node edges =>
      let rows := run (EqualityLeafProjectionCompile.compileEdges leaf edges) state
      have checked := compileEdges_available leaf leaves edges state facts
      have available := makeNode_available rows.1 rows.2 checked.1.coherent checked.1.cached (by
        intro child member
        obtain ⟨edge, included, present⟩ := List.mem_flatMap.mp member
        exact (checked.2 edge included).2 child present)
      have linked := makeNode_linked rows.1 rows.2 checked.1.linked (fun edge member => (checked.2 edge member).1)
      simp only [EqualityLeafProjectionCompile.compile, run_bind]
      exact ⟨⟨available.1, available.2.1, linked⟩, available.2.2⟩
termination_by sizeOf tree

/-- Every original edge request retains its canonical payload and available actual children. -/
theorem compileEdges_available [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (facts : Facts state) :
    let result := run (EqualityLeafProjectionCompile.compileEdges leaf edges) state
    Facts result.2 ∧ ∀ edge ∈ result.1, EdgeResident result.2 edge ∧
      ∀ child ∈ edge.children, Available result.2 child := by
  cases edges with
  | nil => exact ⟨facts, by simp [EqualityLeafProjectionCompile.compileEdges, run]⟩
  | cons edge rest =>
      cases edge with
      | mk tag children =>
          let childResult := run (EqualityLeafProjectionCompile.compileForest leaf children) state
          have childFacts := compileForest_available leaf leaves children state facts
          let edgeResult := run (makeEdge tag.1 tag.2 childResult.1) childResult.2
          have edgeAvailable := makeEdge_available tag.1 tag.2 childResult.1 childResult.2
            childFacts.1.coherent childFacts.1.cached childFacts.2
          have edgeLinked := makeEdge_linked tag.1 tag.2 childResult.1 childResult.2
            childFacts.1.coherent childFacts.1.linked
          have edgeFacts : Facts edgeResult.2 := ⟨edgeAvailable.1, edgeAvailable.2.1, edgeLinked.1⟩
          let tail := run (EqualityLeafProjectionCompile.compileEdges leaf rest) edgeResult.2
          have tailFacts := compileEdges_available leaf leaves rest edgeResult.2 edgeFacts
          have growth : Grows edgeResult.2 tail.2 :=
            (InternedConstructorTemplates.run_correct _ edgeResult.2 edgeFacts.coherent.valid).2
          simp only [EqualityLeafProjectionCompile.compileEdges, run_bind, run]
          refine ⟨tailFacts.1, ?_⟩
          intro selected member
          change selected ∈ edgeResult.1 :: tail.1 at member
          rcases List.mem_cons.mp member with same | later
          · subst selected
            refine ⟨edge_grows edgeResult.2 tail.2 growth edgeResult.1 edgeLinked.2, ?_⟩
            intro child present
            exact available_after_run (EqualityLeafProjectionCompile.compileEdges leaf rest) edgeResult.2
              edgeFacts.coherent.valid (edgeAvailable.2.2 child present)
          · exact tailFacts.2 selected later
termination_by sizeOf edges

/-- Original ordered children remain complete available records after all later siblings. -/
theorem compileForest_available [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (facts : Facts state) :
    let result := run (EqualityLeafProjectionCompile.compileForest leaf forest) state
    Facts result.2 ∧ ∀ value ∈ result.1, Available result.2 value := by
  cases forest with
  | nil => exact ⟨facts, by simp [EqualityLeafProjectionCompile.compileForest, run]⟩
  | cons first rest =>
      let head := run (EqualityLeafProjectionCompile.compile leaf first) state
      have headFacts := compile_available leaf leaves first state facts
      let tail := run (EqualityLeafProjectionCompile.compileForest leaf rest) head.2
      have tailFacts := compileForest_available leaf leaves rest head.2 headFacts.1
      simp only [EqualityLeafProjectionCompile.compileForest, run_bind, run]
      refine ⟨tailFacts.1, ?_⟩
      intro selected member
      change selected ∈ head.1 :: tail.1 at member
      rcases List.mem_cons.mp member with same | later
      · subst selected
        exact available_after_run (EqualityLeafProjectionCompile.compileForest leaf rest) head.2 headFacts.1.coherent.valid headFacts.2
      · exact tailFacts.2 selected later
termination_by sizeOf forest
end

/-- Compiling original children fixes the complete cached edge payload, not only its references. -/
theorem edge_children [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (children : List (Tree (Tag Symbol Guard) Leaf)) (tag : Tag Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) :
    let childResult := run (EqualityLeafProjectionCompile.compileForest leaf children) state
    (run (makeEdge tag.1 tag.2 childResult.1) childResult.2).1.children = childResult.1 := by
  have completed := compileForest_available leaf leaves children state facts
  exact InternedShallowValues.makeEdge_children tag.1 tag.2 _ _ completed.1.coherent completed.1.cached completed.2

/-- Actual nullary row requests preserve every cache payload invariant. -/
theorem nullary_rows_available [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (Symbol × Guard)) (state : State Symbol Guard) (facts : Facts state) :
    let result := run (EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rows)) state
    Facts result.2 ∧ ∀ edge ∈ result.1, EdgeResident result.2 edge := by
  induction rows generalizing state with
  | nil => exact ⟨facts, by simp [EqualityLeafProjectionNullary.requests, EqualityLeafProjectionWorkers.sequence, run]⟩
  | cons first rest ih =>
      rcases first with ⟨symbol, guard⟩
      let head := run (makeEdge symbol guard []) state
      have available := makeEdge_available symbol guard [] state facts.coherent facts.cached (by simp)
      have linked := makeEdge_linked symbol guard [] state facts.coherent facts.linked
      have headFacts : Facts head.2 := ⟨available.1, available.2.1, linked.1⟩
      let tail := run (EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rest)) head.2
      have tailFacts := ih head.2 headFacts
      have growth : Grows head.2 tail.2 := (InternedConstructorTemplates.run_correct _ head.2 headFacts.coherent.valid).2
      simp only [EqualityLeafProjectionNullary.requests, List.map_cons, EqualityLeafProjectionWorkers.sequence, run_bind, run]
      refine ⟨tailFacts.1, ?_⟩
      intro edge member
      change edge ∈ head.1 :: tail.1 at member
      rcases List.mem_cons.mp member with same | later
      · subst edge
        exact edge_grows head.2 tail.2 growth head.1 linked.2
      · exact tailFacts.2 edge later

/-- Generic physical nullary construction supplies complete available output records. -/
theorem nullary_available [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (Symbol × Guard)) (state : State Symbol Guard) (facts : Facts state) :
    Facts (run (EqualityLeafProjectionNullary.build rows) state).2 ∧
      Available (run (EqualityLeafProjectionNullary.build rows) state).2 (run (EqualityLeafProjectionNullary.build rows) state).1 := by
  let compiled := run (EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rows)) state
  have rowsFacts := nullary_rows_available rows state facts
  have rowsExact := EqualityLeafProjectionNullary.completed_rows rows state facts.coherent
  have available := makeNode_available compiled.1 compiled.2 rowsFacts.1.coherent rowsFacts.1.cached (by
    intro child member
    obtain ⟨edge, included, present⟩ := List.mem_flatMap.mp member
    have empty := (rowsExact.2.1 edge included).2
    simp only [empty, List.not_mem_nil] at present)
  have linked := makeNode_linked compiled.1 compiled.2 rowsFacts.1.linked rowsFacts.2
  simp only [EqualityLeafProjectionNullary.build, run_bind]
  exact ⟨⟨available.1, available.2.1, linked⟩, available.2.2⟩

noncomputable local instance : DecidableEq EqualityLeafProjectionLeafCache.ConstraintKey := by classical exact inferInstance

/-- The admitted physical leaf implementation discharges the compiler's local leaf contract. -/
theorem admitted_leaves : LeafAvailable (EqualityLeafProjectionLeafCache.build (initial := initial) (symbols := symbols)) := by
  intro value state facts
  rw [EqualityLeafProjectionProduct.leaf_build]
  exact nullary_available _ state facts

/-- Actual canonical admitted occurrence forests derive all payload invariants without a leaf correctness premise. -/
theorem admitted_forest (forest : List (Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityLeafProjectionLeafCache.Leaf initial symbols)))
    (state : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (facts : Facts state) :
    let result := run (EqualityLeafProjectionCompile.compileForest EqualityLeafProjectionLeafCache.build forest) state
    Facts result.2 ∧ ∀ value ∈ result.1, Available result.2 value :=
  compileForest_available _ admitted_leaves forest state facts

end MicroCFTA.EqualityLeafProjectionCompileAvailability
