import MicroCFTA.EqualityLeafProjectionActualMeet

/-!
# Closed finite-cache representations of original occurrences

A represented occurrence replays its exact complete source record without
allocation in the current cache. Completion establishes this property and
cache growth preserves it. Constructor decomposition derives closed child
requests from the actual completed computation.
-/
namespace MicroCFTA.EqualityLeafProjectionRepresentation
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionSyntax (Tree Edge)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary

/-- The current finite cache replays this occurrence's exact complete record. -/
def Represents [DecidableEq (EdgeKey Symbol Guard)] (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (tree : Tree (Tag Symbol Guard) Leaf) (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  run (EqualityLeafProjectionCompile.compile leaf tree) state = (value, state)

/-- Original ancestor edge requests replay their complete ordered output list. -/
def RepresentsEdges [DecidableEq (EdgeKey Symbol Guard)] (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (edges : List (Edge (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (values : List (EdgeValue Symbol Guard)) : Prop :=
  run (EqualityLeafProjectionCompile.compileEdges leaf edges) state = (values, state)

/-- Original child occurrences replay their complete ordered node list. -/
def RepresentsForest [DecidableEq (EdgeKey Symbol Guard)] (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (values : List (Value Symbol Guard)) : Prop :=
  run (EqualityLeafProjectionCompile.compileForest leaf forest) state = (values, state)

/-- A completed bind makes both actual component requests allocation-free. -/
theorem bind_closed [DecidableEq (EdgeKey Symbol Guard)]
    (first : Work Symbol Guard First) (next : First → Work Symbol Guard Result)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (result : Result) (closed : run (first.bind next) state = (result, state)) :
    ∃ value, run first state = (value, state) ∧ run (next value) state = (result, state) := by
  have growth : Grows (run (first.bind next) state).2 state := by rw [closed]; exact grows_refl state
  have replayed := EqualityLeafProjectionCompile.bind_completed first next state state valid growth
  exact ⟨(run first state).1, replayed.2.1, by simpa only [closed] using replayed.2.2⟩

/-- Once completed, the same physical occurrence remains exact after later cache growth. -/
theorem grows [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (tree : Tree (Tag Symbol Guard) Leaf)
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before) (growth : Grows before after)
    (value : Value Symbol Guard) (represented : Represents leaf tree before value) : Represents leaf tree after value := by
  unfold Represents at represented ⊢
  have requestGrowth : Grows (run (EqualityLeafProjectionCompile.compile leaf tree) before).2 after := by
    rw [represented]
    exact growth
  simpa only [Represents, represented] using replay (EqualityLeafProjectionCompile.compile leaf tree) before after valid requestGrowth

/-- Completed original ancestor rows remain exact after later cache growth. -/
theorem edges_grows [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (edges : List (Edge (Tag Symbol Guard) Leaf))
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before) (growth : Grows before after)
    (values : List (EdgeValue Symbol Guard)) (represented : RepresentsEdges leaf edges before values) : RepresentsEdges leaf edges after values := by
  unfold RepresentsEdges at represented ⊢
  have requestGrowth : Grows (run (EqualityLeafProjectionCompile.compileEdges leaf edges) before).2 after := by
    rw [represented]
    exact growth
  simpa only [RepresentsEdges, represented] using replay (EqualityLeafProjectionCompile.compileEdges leaf edges) before after valid requestGrowth

/-- Completed ordered child occurrences remain exact after later cache growth. -/
theorem forest_grows [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (forest : List (Tree (Tag Symbol Guard) Leaf))
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before) (growth : Grows before after)
    (values : List (Value Symbol Guard)) (represented : RepresentsForest leaf forest before values) : RepresentsForest leaf forest after values := by
  unfold RepresentsForest at represented ⊢
  have requestGrowth : Grows (run (EqualityLeafProjectionCompile.compileForest leaf forest) before).2 after := by
    rw [represented]
    exact growth
  simpa only [RepresentsForest, represented] using replay (EqualityLeafProjectionCompile.compileForest leaf forest) before after valid requestGrowth

/-- Actual finite occurrence execution constructs its own closed representation. -/
theorem completed [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (tree : Tree (Tag Symbol Guard) Leaf)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    let result := run (EqualityLeafProjectionCompile.compile leaf tree) state
    Represents leaf tree result.2 result.1 :=
  replay (EqualityLeafProjectionCompile.compile leaf tree) state _ valid (grows_refl _)

/-- Closed occurrence representations expose complete available physical records. -/
theorem available [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (tree : Tree (Tag Symbol Guard) Leaf) (state : State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (represented : Represents leaf tree state value) : Available state value := by
  have checked := compile_available leaf leaves tree state facts
  rw [represented] at checked
  exact checked.2

/-- Closed ordered child representations expose every complete child record. -/
theorem forest_available [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leaves : LeafAvailable leaf)
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (represented : RepresentsForest leaf forest state values) :
    ∀ value ∈ values, Available state value := by
  have checked := compileForest_available leaf leaves forest state facts
  rw [represented] at checked
  exact checked.2

/-- A represented node exposes its actual finite original edge list and final request. -/
theorem node_decompose [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (edges : List (Edge (Tag Symbol Guard) Leaf))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) (value : Value Symbol Guard)
    (represented : Represents leaf (.node edges) state value) :
    ∃ rows, RepresentsEdges leaf edges state rows ∧ run (makeNode rows) state = (value, state) :=
  bind_closed _ _ state valid value represented

/-- A represented child list exposes each closed source position in its original order. -/
theorem forest_decompose [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (first : Tree (Tag Symbol Guard) Leaf)
    (rest : List (Tree (Tag Symbol Guard) Leaf)) (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (values : List (Value Symbol Guard)) (represented : RepresentsForest leaf (first :: rest) state values) :
    ∃ value tail, values = value :: tail ∧ Represents leaf first state value ∧ RepresentsForest leaf rest state tail := by
  obtain ⟨value, head, later⟩ := bind_closed _ _ state valid values represented
  obtain ⟨tail, remaining, result⟩ := bind_closed _ _ state valid values later
  have equal : values = value :: tail := (congrArg (fun result : List (Value Symbol Guard) × State Symbol Guard => result.1) result).symm
  exact ⟨value, tail, equal, head, remaining⟩

/-- Original edge decomposition retains exact tags, child order, and the actual edge request. -/
theorem edges_decompose [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (tag : Tag Symbol Guard)
    (children : List (Tree (Tag Symbol Guard) Leaf)) (rest : List (Edge (Tag Symbol Guard) Leaf))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (values : List (EdgeValue Symbol Guard)) (represented : RepresentsEdges leaf (.mk tag children :: rest) state values) :
    ∃ nodes edge tail, values = edge :: tail ∧ RepresentsForest leaf children state nodes ∧
      run (makeEdge tag.1 tag.2 nodes) state = (edge, state) ∧ RepresentsEdges leaf rest state tail := by
  obtain ⟨nodes, childClosed, later⟩ := bind_closed _ _ state valid values represented
  obtain ⟨edge, edgeClosed, restClosed⟩ := bind_closed _ _ state valid values later
  obtain ⟨tail, remaining, result⟩ := bind_closed _ _ state valid values restClosed
  have equal : values = edge :: tail := (congrArg (fun result : List (EdgeValue Symbol Guard) × State Symbol Guard => result.1) result).symm
  exact ⟨nodes, edge, tail, equal, childClosed, edgeClosed, remaining⟩

/-- Reconstruct a closed parent from the exact original edge requests. -/
theorem node_intro [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (edges : List (Edge (Tag Symbol Guard) Leaf))
    (state : State Symbol Guard) (value : Value Symbol Guard) (rows : List (EdgeValue Symbol Guard))
    (represented : RepresentsEdges leaf edges state rows) (node : run (makeNode rows) state = (value, state)) :
    Represents leaf (.node edges) state value := by
  unfold RepresentsEdges at represented
  simp only [Represents, EqualityLeafProjectionCompile.compile, run_bind, represented, node]

/-- Reconstruct the exact original child order from its closed head and tail. -/
theorem forest_intro [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (first : Tree (Tag Symbol Guard) Leaf)
    (rest : List (Tree (Tag Symbol Guard) Leaf)) (state : State Symbol Guard)
    (value : Value Symbol Guard) (tail : List (Value Symbol Guard))
    (head : Represents leaf first state value) (remaining : RepresentsForest leaf rest state tail) :
    RepresentsForest leaf (first :: rest) state (value :: tail) := by
  unfold Represents at head
  unfold RepresentsForest at remaining
  simp only [RepresentsForest, EqualityLeafProjectionCompile.compileForest, run_bind, head, remaining, run]

/-- Reconstruct original ancestor rows with their exact complete source request. -/
theorem edges_intro [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (tag : Tag Symbol Guard)
    (children : List (Tree (Tag Symbol Guard) Leaf)) (rest : List (Edge (Tag Symbol Guard) Leaf))
    (state : State Symbol Guard) (nodes : List (Value Symbol Guard)) (edge : EdgeValue Symbol Guard) (tail : List (EdgeValue Symbol Guard))
    (childClosed : RepresentsForest leaf children state nodes) (edgeClosed : run (makeEdge tag.1 tag.2 nodes) state = (edge, state))
    (remaining : RepresentsEdges leaf rest state tail) : RepresentsEdges leaf (.mk tag children :: rest) state (edge :: tail) := by
  unfold RepresentsForest at childClosed
  unfold RepresentsEdges at remaining
  simp only [RepresentsEdges, EqualityLeafProjectionCompile.compileEdges, run_bind, childClosed, edgeClosed, remaining, run]

/-- Represented physical child lists retain the original constructor arity. -/
theorem forest_length [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (forest : List (Tree (Tag Symbol Guard) Leaf))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) (values : List (Value Symbol Guard))
    (represented : RepresentsForest leaf forest state values) : values.length = forest.length := by
  have requestGrowth : Grows (run (EqualityLeafProjectionCompile.compileForest leaf forest) state).2 state := by
    rw [represented]
    exact grows_refl state
  have exactLower := EqualityLeafProjectionCompile.compileForest_lower leaf (fun _ value => .pure value) forest state state valid requestGrowth
  rw [represented] at exactLower
  dsimp only at exactLower
  rw [← exactLower]
  exact EqualityLeafProjectionSyntax.lowerForest_length _ forest

/-- A closed edge request retains its complete source tag and exact ordered child records. -/
theorem edge_fields [DecidableEq (EdgeKey Symbol Guard)]
    (tag : Tag Symbol Guard) (nodes : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : ∀ value ∈ nodes, Available state value) (edge : EdgeValue Symbol Guard)
    (closed : run (makeEdge tag.1 tag.2 nodes) state = (edge, state)) :
    edge.entry.key.symbol = tag.1 ∧ edge.entry.key.constraint = tag.2 ∧ edge.children = nodes := by
  let key : EdgeKey Symbol Guard := ⟨tag.1, nodes.map Value.referenceOf, tag.2⟩
  let identify := fun entry => EdgeValue.mk entry nodes
  have correct := edgeStep_correct key identify state facts.coherent.valid
  have after := edgeStep_coherent key identify state facts.coherent (fun _ same => ⟨rfl, same, rfl⟩)
  have fields := (after.edges _ _ correct.2.2).2.1
  have requested : (run (makeEdge tag.1 tag.2 nodes) state).1.entry.key = key := fields
  have children := InternedShallowValues.makeEdge_children tag.1 tag.2 nodes state facts.coherent facts.cached available
  rw [closed] at requested children
  exact ⟨congrArg EdgeKey.symbol requested, congrArg EdgeKey.constraint requested, children⟩

end MicroCFTA.EqualityLeafProjectionRepresentation
