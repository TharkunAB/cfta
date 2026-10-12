import MicroCFTA.EqualityLeafProjectionCompileOrdinary

/-!
# Complete cache payloads through actual required-path execution

Required-path workers preserve complete child availability and stored
node-edge links. The proof follows their actual optional branches and
ordered effects. Unsupported constructors can return none; retained
ordinary records therefore use the existing completion theorem separately.
-/
namespace MicroCFTA.EqualityLeafProjectionRequireAvailability
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionWorkers
open EqualityLeafProjectionSyntax (Path descend fits)

/-- Successful optional results carry a selected complete-payload property. -/
def Checked [DecidableEq (EdgeKey Symbol Guard)] (property : State Symbol Guard → Result → Prop)
    (work : Work Symbol Guard (Option Result)) (state : State Symbol Guard) : Prop :=
  let result := run work state
  Facts result.2 ∧ ∀ value, result.1 = some value → property result.2 value

/-- Available ordered result lists preserve every complete child record. -/
def ChildrenAvailable (state : State Symbol Guard) (values : List (Value Symbol Guard)) : Prop :=
  ∀ value ∈ values, Available state value

/-- Rebuilt result lists retain canonical edges and complete actual child records. -/
def EdgesAvailable (state : State Symbol Guard) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, EdgeResident state edge ∧ ChildrenAvailable state edge.children

/-- Optional sequencing preserves cache facts on both success and failure. -/
theorem bindOptional_checked [DecidableEq (EdgeKey Symbol Guard)]
    (first : Work Symbol Guard (Option First)) (next : First → Work Symbol Guard (Option Result))
    (state : State Symbol Guard) (input : State Symbol Guard → First → Prop)
    (output : State Symbol Guard → Result → Prop)
    (checked : Checked input first state)
    (later : ∀ value, input (run first state).2 value → Checked output (next value) (run first state).2) :
    Checked output (bindOptional first next) state := by
  cases found : (run first state).1 with
  | none =>
      simp only [Checked, bindOptional, run_bind, found, run]
      exact ⟨checked.1, by intro value impossible; cases impossible⟩
  | some value =>
      simpa only [Checked, bindOptional, run_bind, found] using later value (checked.2 value found)

/-- Actual parent construction preserves complete available edge and child payloads. -/
theorem node_checked [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : EdgesAvailable state edges) :
    Checked Available ((makeNode edges).bind fun value => .pure (some value)) state := by
  have result := makeNode_available edges state facts.coherent facts.cached (by
    intro child member
    obtain ⟨edge, included, present⟩ := List.mem_flatMap.mp member
    exact (available edge included).2 child present)
  have linked := makeNode_linked edges state facts.linked (fun edge member => (available edge member).1)
  simp only [Checked, run_bind, run]
  refine ⟨⟨result.1, result.2.1, linked⟩, ?_⟩
  intro value same
  cases Option.some.inj same
  exact result.2.2

mutual
/-- Every required-path branch preserves complete available payloads on success. -/
theorem require_available [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) : Checked Available (require paths value) state := by
  unfold require
  split
  · simp only [Checked, run]
    exact ⟨facts, by intro result same; cases Option.some.inj same; exact available⟩
  · cases value with
    | empty =>
        simp only [Checked, run]
        exact ⟨facts, by intro result same; cases Option.some.inj same; exact empty_available state⟩
    | reference | union | mu =>
        simp only [Checked, run]
        exact ⟨facts, by intro result impossible; cases impossible⟩
    | node entry edges depth free =>
        have children : ∀ edge ∈ edges, ChildrenAvailable state edge.children := by
          intro edge included child present
          exact available.children child (List.mem_flatMap.mpr ⟨edge, included, present⟩)
        have rows := requireEdges_available paths edges state facts children
        exact bindOptional_checked _ _ state EdgesAvailable Available rows
          (fun edges present => node_checked edges _ rows.1 present)
termination_by sizeOf value

/-- Required-path row filtering preserves links and child payloads before later rows execute. -/
theorem requireEdges_available [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : ∀ edge ∈ edges, ChildrenAvailable state edge.children) :
    Checked EdgesAvailable (requireEdges paths edges) state := by
  cases edges with
  | nil =>
      simp only [requireEdges, Checked, run]
      exact ⟨facts, by intro value same; cases Option.some.inj same; simp [EdgesAvailable]⟩
  | cons edge rest =>
      cases edge with
      | mk entry original =>
          unfold requireEdges
          split
          · let children := run (requireChildren paths 0 original) state
            have checked := requireChildren_available paths 0 original state facts (available (.mk entry original) (by simp))
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
              have afterChildren := available_after_run (requireChildren paths 0 original) state facts.coherent.valid originalAvailable
              exact available_after_run (makeEdge entry.key.symbol entry.key.constraint values) children.2 checked.1.coherent.valid afterChildren
            have tail := requireEdges_available paths rest rebuilt.2 edgeFacts restAvailable
            simp only [Checked, run_bind]
            change Checked EdgesAvailable (bindOptional (requireEdges paths rest) (fun edges => .pure (some (rebuilt.1 :: edges)))) rebuilt.2
            apply bindOptional_checked _ _ rebuilt.2 EdgesAvailable EdgesAvailable tail
            intro edges edgesAvailable
            simp only [Checked, run]
            refine ⟨tail.1, ?_⟩
            intro result same
            cases Option.some.inj same
            intro edge member
            rcases List.mem_cons.mp member with equal | later
            · subst edge
              have growth := (InternedConstructorTemplates.run_correct (requireEdges paths rest) rebuilt.2 edgeFacts.coherent.valid).2
              refine ⟨edge_grows _ _ growth _ edgeLinked.2, ?_⟩
              intro child present
              exact available_after_run (requireEdges paths rest) rebuilt.2 edgeFacts.coherent.valid (edgeAvailable.2.2 child present)
            · exact edgesAvailable edge later
          · exact requireEdges_available paths rest state facts (fun edge member => available edge (by simp [member]))
termination_by sizeOf edges

/-- Ordered child requirements preserve all earlier complete output records. -/
theorem requireChildren_available [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (index : Nat) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : ChildrenAvailable state values) :
    Checked ChildrenAvailable (requireChildren paths index values) state := by
  cases values with
  | nil =>
      simp only [requireChildren, Checked, run]
      exact ⟨facts, by intro result same; cases Option.some.inj same; simp [ChildrenAvailable]⟩
  | cons child rest =>
      let head := run (require (descend paths index) child) state
      have checked := require_available (descend paths index) child state facts (available child (by simp))
      rw [requireChildren]
      apply bindOptional_checked _ _ state Available ChildrenAvailable checked
      intro value valueAvailable
      have restAvailable : ChildrenAvailable head.2 rest := by
        intro other member
        exact available_after_run (require (descend paths index) child) state facts.coherent.valid (available other (by simp [member]))
      have tail := requireChildren_available paths (index + 1) rest head.2 checked.1 restAvailable
      apply bindOptional_checked _ _ head.2 ChildrenAvailable ChildrenAvailable tail
      intro values valuesAvailable
      simp only [Checked, run]
      refine ⟨tail.1, ?_⟩
      intro result same
      cases Option.some.inj same
      intro selected member
      rcases List.mem_cons.mp member with equal | later
      · subst selected
        exact available_after_run (requireChildren paths (index + 1) rest) head.2 checked.1.coherent.valid valueAvailable
      · exact valuesAvailable selected later
termination_by sizeOf values
end

end MicroCFTA.EqualityLeafProjectionRequireAvailability
