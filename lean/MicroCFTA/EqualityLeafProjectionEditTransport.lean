import MicroCFTA.EqualityLeafProjectionEditClosed

/-!
# Ordered recursive transport of closed simultaneous edits

Selected paths stop at leaf domains. Completed source requests retain
original child positions across each finite cache extension.
-/
namespace MicroCFTA.EqualityLeafProjectionEditTransport
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Tree Edge Path descendEdits Admissible ChildAt descendEdits_member)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkers
open EqualityLeafProjectionClosedWorkers

/-- Recursive edit correspondence represents the actual result in a finite later cache. -/
def Transport [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (join : Leaf → Leaf → Leaf) (tree : Tree (Tag Symbol Guard) Leaf) : Prop :=
  ∀ edits, Admissible edits tree → ∀ state, Facts state → ∀ value, Represents leaf tree state value →
    let actual := run (edit meet edits value) state
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents leaf (EqualityLeafProjectionSyntax.edit join edits tree) after result

/-- Strict child correspondence composes through closed ordered source edits. -/
theorem closed_children [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (join : Leaf → Leaf → Leaf)
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (each : ∀ child ∈ forest, Transport leaf meet join child)
    (edits : List (Path × Leaf)) (index : Nat)
    (admissible : ∀ offset path target, ((index + offset) :: path, target) ∈ edits → ChildAt offset path forest)
    (state : State Symbol Guard) (facts : Facts state) (values results : List (Value Symbol Guard))
    (represented : RepresentsForest leaf forest state values)
    (closed : run (editChildren meet edits index values) state = (some results, state)) :
    ∃ after, Facts after ∧ Grows state after ∧
      RepresentsForest leaf (EqualityLeafProjectionSyntax.editChildren join edits index forest) after results := by
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
      have headValid : Admissible (descendEdits edits index) first := by
        intro path target present
        exact admissible 0 path target (by simpa using descendEdits_member edits index path target present)
      have tailValid : ∀ offset path target, ((index + 1 + offset) :: path, target) ∈ edits → ChildAt offset path rest := by
        intro offset path target present
        exact admissible (offset + 1) path target (by simpa [Nat.add_assoc, Nat.add_comm 1 offset] using present)
      obtain ⟨value, tail, rfl, headRep, tailRep⟩ := forest_decompose leaf first rest state facts.coherent.valid values represented
      obtain ⟨result, remaining, rfl, headClosed, tailClosed⟩ :=
        EqualityLeafProjectionEditClosed.children_decompose meet edits index value tail state facts.coherent.valid results closed
      obtain ⟨middle, actual, middleFacts, middleGrowth, returned, headChanged⟩ :=
        each first (by simp) (descendEdits edits index) headValid state facts value headRep
      rw [headClosed] at middleGrowth returned
      have same : result = actual := Option.some.inj returned
      subst actual
      have laterTail := forest_grows leaf rest state middle facts.coherent.valid middleGrowth tail tailRep
      have laterClosed := work_grows (editChildren meet edits (index + 1) tail) state middle facts.coherent.valid
        (some remaining) tailClosed middleGrowth
      obtain ⟨after, afterFacts, afterGrowth, tailChanged⟩ := ih
        (fun child member => each child (by simp [member])) (index + 1) tailValid middle middleFacts tail remaining laterTail laterClosed
      have headLater := EqualityLeafProjectionRepresentation.grows leaf (EqualityLeafProjectionSyntax.edit join (descendEdits edits index) first)
        middle after middleFacts.coherent.valid afterGrowth result headChanged
      refine ⟨after, afterFacts, grows_trans middleGrowth afterGrowth, ?_⟩
      exact forest_intro leaf _ _ after result remaining headLater tailChanged

/-- Original edge occurrences retain their tags and positions through actual closed edits. -/
theorem closed_edges [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf)
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (join : Leaf → Leaf → Leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf))
    (each : ∀ edge ∈ edges, ∀ child ∈ edge.children, Transport leaf meet join child)
    (edits : List (Path × Leaf)) (admissible : Admissible edits (.node edges))
    (state : State Symbol Guard) (facts : Facts state)
    (rows results : List (EdgeValue Symbol Guard)) (represented : RepresentsEdges leaf edges state rows)
    (closed : run (editEdges meet edits rows) state = (some results, state)) :
    ∃ after, Facts after ∧ Grows state after ∧
      RepresentsEdges leaf (EqualityLeafProjectionSyntax.editEdges join edits edges) after results := by
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
          have tailValid : Admissible edits (.node rest) := by
            intro path target present
            cases path with
            | nil => exact admissible _ _ present
            | cons index path => exact (admissible _ _ present).2
          have childrenValid : ∀ index path target, (index :: path, target) ∈ edits → ChildAt index path children := by
            intro index path target present
            exact (admissible _ _ present).1
          obtain ⟨nodes, edge, tail, rfl, childrenRep, edgeClosed, tailRep⟩ :=
            EqualityLeafProjectionRepresentation.edges_decompose leaf tag children rest state facts.coherent.valid rows represented
          have inputAvailable := forest_available leaf leafAvailable children state facts nodes childrenRep
          have fields := edge_fields tag nodes state facts inputAvailable edge edgeClosed
          cases edge with
          | mk entry original =>
              have sameChildren : original = nodes := fields.2.2
              subst original
              have symbol : entry.key.symbol = tag.1 := fields.1
              have guard : entry.key.constraint = tag.2 := fields.2.1
              obtain ⟨updated, result, remaining, rfl, childClosed, resultClosed, tailClosed⟩ :=
                EqualityLeafProjectionEditClosed.edges_decompose meet edits entry nodes tail state facts.coherent.valid results closed
              obtain ⟨middle, middleFacts, middleGrowth, childrenChanged⟩ := closed_children leaf meet join children
                (fun child member => each (.mk tag children) (by simp) child member) edits 0 (by simpa using childrenValid)
                state facts nodes updated childrenRep childClosed
              have laterTail := edges_grows leaf rest state middle facts.coherent.valid middleGrowth tail tailRep
              have laterClosed := work_grows (editEdges meet edits tail) state middle facts.coherent.valid
                (some remaining) tailClosed middleGrowth
              obtain ⟨after, afterFacts, afterGrowth, tailChanged⟩ := ih
                (fun edge member child present => each edge (by simp [member]) child present)
                tailValid middle middleFacts tail remaining laterTail laterClosed
              have childrenLater := forest_grows leaf (EqualityLeafProjectionSyntax.editChildren join edits 0 children)
                middle after middleFacts.coherent.valid afterGrowth updated childrenChanged
              have requested : run (makeEdge tag.1 tag.2 updated) state = (result, state) := by
                simpa only [symbol, guard] using resultClosed
              have edgeLater := work_grows (makeEdge tag.1 tag.2 updated) state after facts.coherent.valid result requested
                (grows_trans middleGrowth afterGrowth)
              refine ⟨after, afterFacts, grows_trans middleGrowth afterGrowth, ?_⟩
              exact edges_intro leaf tag _ _ after updated result remaining childrenLater edgeLater tailChanged

end MicroCFTA.EqualityLeafProjectionEditTransport
