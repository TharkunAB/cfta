import MicroCFTA.EqualityLeafProjectionClosedWorkers

/-!
# Ordered recursive transport of closed required-path results

Each strict child occurrence gets a represented result in a finite later
cache. Completed source child requests replay across these extensions, so
proof preparation does not change the earlier source result or its order.
-/
namespace MicroCFTA.EqualityLeafProjectionRequireTransport
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Tree Edge Path fits descend)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkers
open EqualityLeafProjectionRequireAvailability EqualityLeafProjectionClosedWorkers

/-- Recursive requirement correspondence retains the actual source result in a finite later cache. -/
def Transport [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (tree : Tree (Tag Symbol Guard) Leaf) : Prop :=
  ∀ paths state, Facts state → ∀ value, Represents leaf tree state value →
    let actual := run (require paths value) state
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents leaf (EqualityLeafProjectionSyntax.require paths tree) after result

/-- Strict-child correspondence composes through actual closed ordered requirement results. -/
theorem closed_children [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (forest : List (Tree (Tag Symbol Guard) Leaf))
    (each : ∀ child ∈ forest, Transport leaf child) (paths : List Path) (index : Nat)
    (state : State Symbol Guard) (facts : Facts state) (values results : List (Value Symbol Guard))
    (represented : RepresentsForest leaf forest state values)
    (closed : run (requireChildren paths index values) state = (some results, state)) :
    ∃ after, Facts after ∧ Grows state after ∧
      RepresentsForest leaf (EqualityLeafProjectionSyntax.requireChildren paths index forest) after results := by
  induction forest generalizing index state values results with
  | nil =>
      have input : values = [] := by
        have same := congrArg (fun result : List (Value Symbol Guard) × State Symbol Guard => result.1) represented
        exact same.symm
      subst values
      have output : results = [] := by
        have same := congrArg (fun result : Option (List (Value Symbol Guard)) × State Symbol Guard => result.1) closed
        exact (Option.some.inj same).symm
      subst results
      exact ⟨state, facts, grows_refl state, rfl⟩
  | cons first rest ih =>
      obtain ⟨value, tail, rfl, headRep, tailRep⟩ := forest_decompose leaf first rest state facts.coherent.valid values represented
      obtain ⟨result, remaining, rfl, headClosed, tailClosed⟩ := children_decompose paths index value tail state facts.coherent.valid results closed
      obtain ⟨middle, actual, middleFacts, middleGrowth, returned, headChanged⟩ :=
        each first (by simp) (descend paths index) state facts value headRep
      rw [headClosed] at middleGrowth returned
      have same : result = actual := Option.some.inj returned
      subst actual
      have laterTail := forest_grows leaf rest state middle facts.coherent.valid middleGrowth tail tailRep
      have laterClosed := work_grows (requireChildren paths (index + 1) tail) state middle facts.coherent.valid
        (some remaining) tailClosed middleGrowth
      obtain ⟨after, afterFacts, afterGrowth, tailChanged⟩ := ih
        (fun child member => each child (by simp [member])) (index + 1) middle middleFacts tail remaining laterTail laterClosed
      have headLater := EqualityLeafProjectionRepresentation.grows leaf (EqualityLeafProjectionSyntax.require (descend paths index) first)
        middle after middleFacts.coherent.valid afterGrowth result headChanged
      refine ⟨after, afterFacts, grows_trans middleGrowth afterGrowth, ?_⟩
      exact forest_intro leaf _ _ after result remaining headLater tailChanged

/-- Source child execution runs before finite recursive proof preparation. Its
complete ordered result gets the changed occurrence representation. -/
theorem children [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf) (leafOrdinary : LeafOrdinary leaf)
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (each : ∀ child ∈ forest, Transport leaf child)
    (paths : List Path) (index : Nat) (state : State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (represented : RepresentsForest leaf forest state values) :
    let actual := run (requireChildren paths index values) state
    ∃ after results, Facts after ∧ Grows actual.2 after ∧ actual.1 = some results ∧
      RepresentsForest leaf (EqualityLeafProjectionSyntax.requireChildren paths index forest) after results := by
  let actual := run (requireChildren paths index values) state
  have inputAvailable := forest_available leaf leafAvailable forest state facts values represented
  have inputOrdinary := compileForest_ordinary leaf leafAvailable leafOrdinary forest state facts
  rw [represented] at inputOrdinary
  have convert : ∀ nodes : List (Value Symbol Guard), (∀ node ∈ nodes, EqualityLeafProjectionWorkers.Ordinary node) → OrdinaryChildren nodes := by
    intro nodes all
    induction nodes with
    | nil => trivial
    | cons node rest ih => exact ⟨all node (by simp), ih (fun other member => all other (by simp [member]))⟩
  have ordinary : OrdinaryChildren values := convert values inputOrdinary
  have checked := requireChildren_available paths index values state facts inputAvailable
  obtain ⟨results, returned⟩ := requireChildren_returns paths index values ordinary state
  have currentGrowth : Grows state actual.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have laterRep := forest_grows leaf forest state actual.2 facts.coherent.valid currentGrowth values represented
  have closed : run (requireChildren paths index values) actual.2 = (some results, actual.2) := by
    simpa only [returned] using replay (requireChildren paths index values) state actual.2 facts.coherent.valid (grows_refl actual.2)
  obtain ⟨after, afterFacts, afterGrowth, changed⟩ := closed_children leaf forest each paths index actual.2 checked.1 values results laterRep closed
  exact ⟨after, results, afterFacts, afterGrowth, returned, changed⟩

/-- Strict-child correspondence composes through original row filtering and
closed actual edge requests, retaining duplicate and dead occurrence rows. -/
theorem closed_edges [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf))
    (each : ∀ edge ∈ edges, ∀ child ∈ edge.children, Transport leaf child)
    (paths : List Path) (state : State Symbol Guard) (facts : Facts state)
    (rows results : List (EdgeValue Symbol Guard)) (represented : RepresentsEdges leaf edges state rows)
    (closed : run (requireEdges paths rows) state = (some results, state)) :
    ∃ after, Facts after ∧ Grows state after ∧
      RepresentsEdges leaf (EqualityLeafProjectionSyntax.requireEdges paths edges) after results := by
  induction edges generalizing state rows results with
  | nil =>
      have input : rows = [] := by
        have same := congrArg (fun result : List (EdgeValue Symbol Guard) × State Symbol Guard => result.1) represented
        exact same.symm
      subst rows
      have output : results = [] := by
        have same := congrArg (fun result : Option (List (EdgeValue Symbol Guard)) × State Symbol Guard => result.1) closed
        exact (Option.some.inj same).symm
      subst results
      exact ⟨state, facts, grows_refl state, rfl⟩
  | cons first rest ih =>
      cases first with
      | mk tag children =>
          obtain ⟨nodes, edge, tail, rfl, childrenRep, edgeClosed, tailRep⟩ :=
            EqualityLeafProjectionRepresentation.edges_decompose leaf tag children rest state facts.coherent.valid rows represented
          have inputAvailable := forest_available leaf leafAvailable children state facts nodes childrenRep
          have fields := edge_fields tag nodes state facts inputAvailable edge edgeClosed
          have arity := forest_length leaf children state facts.coherent.valid nodes childrenRep
          cases edge with
          | mk entry original =>
              have sameChildren : original = nodes := fields.2.2
              subst original
              have symbol : entry.key.symbol = tag.1 := fields.1
              have guard : entry.key.constraint = tag.2 := fields.2.1
              by_cases accepted : fits paths children.length = true
              · have selected : fits paths nodes.length = true := by rw [arity]; exact accepted
                obtain ⟨updated, result, remaining, rfl, childClosed, resultClosed, tailClosed⟩ :=
                  EqualityLeafProjectionClosedWorkers.edges_decompose paths entry nodes tail selected state facts.coherent.valid results closed
                obtain ⟨middle, middleFacts, middleGrowth, childrenChanged⟩ := closed_children leaf children
                  (fun child member => each (.mk tag children) (by simp) child member) paths 0 state facts nodes updated childrenRep childClosed
                have laterTail := edges_grows leaf rest state middle facts.coherent.valid middleGrowth tail tailRep
                have laterClosed := work_grows (requireEdges paths tail) state middle facts.coherent.valid
                  (some remaining) tailClosed middleGrowth
                obtain ⟨after, afterFacts, afterGrowth, tailChanged⟩ := ih
                  (fun edge member child present => each edge (by simp [member]) child present)
                  middle middleFacts tail remaining laterTail laterClosed
                have childrenLater := forest_grows leaf (EqualityLeafProjectionSyntax.requireChildren paths 0 children)
                  middle after middleFacts.coherent.valid afterGrowth updated childrenChanged
                have requested : run (makeEdge tag.1 tag.2 updated) state = (result, state) := by
                  simpa only [symbol, guard] using resultClosed
                have edgeLater := work_grows (makeEdge tag.1 tag.2 updated) state after facts.coherent.valid result requested
                  (grows_trans middleGrowth afterGrowth)
                refine ⟨after, afterFacts, grows_trans middleGrowth afterGrowth, ?_⟩
                simp only [EqualityLeafProjectionSyntax.requireEdges, accepted, ↓reduceIte]
                exact edges_intro leaf tag _ _ after updated result remaining childrenLater edgeLater tailChanged
              · have rejected : fits paths nodes.length = false := by rw [arity]; exact Bool.eq_false_iff.mpr accepted
                have tailClosed : run (requireEdges paths tail) state = (some results, state) := by
                  simpa only [requireEdges, rejected, Bool.false_eq_true, ↓reduceIte] using closed
                obtain ⟨after, afterFacts, afterGrowth, tailChanged⟩ := ih
                  (fun edge member child present => each edge (by simp [member]) child present)
                  state facts tail results tailRep tailClosed
                refine ⟨after, afterFacts, afterGrowth, ?_⟩
                simpa only [EqualityLeafProjectionSyntax.requireEdges, accepted, Bool.false_eq_true, ↓reduceIte] using tailChanged

end MicroCFTA.EqualityLeafProjectionRequireTransport
