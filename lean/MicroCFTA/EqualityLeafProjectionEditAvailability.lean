import MicroCFTA.EqualityLeafProjectionRequireAvailability

/-!
# Complete cache payloads through actual leaf editing

The finite edit workers preserve complete available child records and
stored node-edge links. Only the local leaf-intersection constructor has
an availability premise. Parent reconstruction and optional failures are
derived from the actual ordered source effects.
-/
namespace MicroCFTA.EqualityLeafProjectionEditAvailability
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionWorkers EqualityLeafProjectionRequireAvailability
open EqualityLeafProjectionSyntax (Path descendEdits)

/-- Local leaf intersection preserves the complete source cache payloads. -/
def MeetAvailable [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ target value state, Facts state → Available state value →
    Facts (run (meet target value) state).2 ∧ Available (run (meet target value) state).2 (run (meet target value) state).1

mutual
/-- Actual edit branches preserve complete available result payloads. -/
theorem edit_available [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (meetAvailable : MeetAvailable meet)
    (edits : List (Path × Target)) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) : Checked Available (edit meet edits value) state := by
  cases edits with
  | nil =>
      simp only [edit, Checked, run]
      exact ⟨facts, by intro result same; cases Option.some.inj same; exact available⟩
  | cons first rest =>
      cases value with
      | empty =>
          simp only [edit_empty, Checked, run]
          exact ⟨facts, by intro result same; cases Option.some.inj same; exact empty_available state⟩
      | reference | union | mu =>
          simp only [edit, Checked, run]
          exact ⟨facts, by intro result impossible; cases impossible⟩
      | node entry edges depth free =>
          rw [edit]
          split
          · rename_i target found
            have checked := meetAvailable target (.node entry edges depth free) state facts available
            simp only [Checked, run_bind, run]
            exact ⟨checked.1, by intro result same; cases Option.some.inj same; exact checked.2⟩
          · have children : ∀ edge ∈ edges, ChildrenAvailable state edge.children := by
              intro edge included child present
              exact available.children child (List.mem_flatMap.mpr ⟨edge, included, present⟩)
            have rows := editEdges_available meet meetAvailable (first :: rest) edges state facts children
            exact bindOptional_checked _ _ state EdgesAvailable Available rows
              (fun edges present => node_checked edges _ rows.1 present)
termination_by sizeOf value

/-- Edited ancestor rows retain canonical links and complete child payloads. -/
theorem editEdges_available [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (meetAvailable : MeetAvailable meet)
    (edits : List (Path × Target)) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : ∀ edge ∈ edges, ChildrenAvailable state edge.children) :
    Checked EdgesAvailable (editEdges meet edits edges) state := by
  cases edges with
  | nil =>
      simp only [editEdges, Checked, run]
      exact ⟨facts, by intro value same; cases Option.some.inj same; simp [EdgesAvailable]⟩
  | cons edge rest =>
      cases edge with
      | mk entry original =>
          rw [editEdges]
          let children := run (editChildren meet edits 0 original) state
          have checked := editChildren_available meet meetAvailable edits 0 original state facts (available (.mk entry original) (by simp))
          apply bindOptional_checked _ _ state ChildrenAvailable EdgesAvailable checked
          intro values valuesAvailable
          let rebuilt := run (makeEdge entry.key.symbol entry.key.constraint values) children.2
          have edgeAvailable := makeEdge_available entry.key.symbol entry.key.constraint values children.2
            checked.1.coherent checked.1.cached valuesAvailable
          have edgeLinked := makeEdge_linked entry.key.symbol entry.key.constraint values children.2
            checked.1.coherent checked.1.linked
          have edgeFacts : Facts rebuilt.2 := ⟨edgeAvailable.1, edgeAvailable.2.1, edgeLinked.1⟩
          have restAvailable : ∀ edge ∈ rest, ChildrenAvailable rebuilt.2 edge.children := by
            intro edge member child present
            have originalAvailable := available edge (by simp [member]) child present
            have afterChildren := available_after_run (editChildren meet edits 0 original) state facts.coherent.valid originalAvailable
            exact available_after_run (makeEdge entry.key.symbol entry.key.constraint values) children.2 checked.1.coherent.valid afterChildren
          have tail := editEdges_available meet meetAvailable edits rest rebuilt.2 edgeFacts restAvailable
          simp only [Checked, run_bind]
          change Checked EdgesAvailable (bindOptional (editEdges meet edits rest) (fun edges => .pure (some (rebuilt.1 :: edges)))) rebuilt.2
          apply bindOptional_checked _ _ rebuilt.2 EdgesAvailable EdgesAvailable tail
          intro edges edgesAvailable
          simp only [Checked, run]
          refine ⟨tail.1, ?_⟩
          intro result same
          cases Option.some.inj same
          intro edge member
          rcases List.mem_cons.mp member with equal | later
          · subst edge
            have growth := (InternedConstructorTemplates.run_correct (editEdges meet edits rest) rebuilt.2 edgeFacts.coherent.valid).2
            refine ⟨edge_grows _ _ growth _ edgeLinked.2, ?_⟩
            intro child present
            exact available_after_run (editEdges meet edits rest) rebuilt.2 edgeFacts.coherent.valid (edgeAvailable.2.2 child present)
          · exact edgesAvailable edge later
termination_by sizeOf edges

/-- Ordered child edits preserve all earlier complete output records. -/
theorem editChildren_available [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (meetAvailable : MeetAvailable meet)
    (edits : List (Path × Target)) (index : Nat) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : ChildrenAvailable state values) :
    Checked ChildrenAvailable (editChildren meet edits index values) state := by
  cases values with
  | nil =>
      simp only [editChildren, Checked, run]
      exact ⟨facts, by intro result same; cases Option.some.inj same; simp [ChildrenAvailable]⟩
  | cons child rest =>
      let head := run (edit meet (descendEdits edits index) child) state
      have checked := edit_available meet meetAvailable (descendEdits edits index) child state facts (available child (by simp))
      rw [editChildren]
      apply bindOptional_checked _ _ state Available ChildrenAvailable checked
      intro value valueAvailable
      have restAvailable : ChildrenAvailable head.2 rest := by
        intro other member
        exact available_after_run (edit meet (descendEdits edits index) child) state facts.coherent.valid (available other (by simp [member]))
      have tail := editChildren_available meet meetAvailable edits (index + 1) rest head.2 checked.1 restAvailable
      apply bindOptional_checked _ _ head.2 ChildrenAvailable ChildrenAvailable tail
      intro values valuesAvailable
      simp only [Checked, run]
      refine ⟨tail.1, ?_⟩
      intro result same
      cases Option.some.inj same
      intro selected member
      rcases List.mem_cons.mp member with equal | later
      · subst selected
        exact available_after_run (editChildren meet edits (index + 1) rest) head.2 checked.1.coherent.valid valueAvailable
      · exact valuesAvailable selected later
termination_by sizeOf values
end

end MicroCFTA.EqualityLeafProjectionEditAvailability
