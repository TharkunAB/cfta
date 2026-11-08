import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
import MicroCFTA.SourceSynthesisAnnotationFieldConstructors

/-!
# Type fields at every physical Program position

The certificate retains each complete source row. All Type operands have
annotations. Program operands have the same certificate recursively.
Program values are empty or ordinary. Actual union construction preserves
this shape through its empty, singleton, and ordinary-node branches.
-/
namespace MicroCFTA.SourceSynthesisHereditaryProgramFields
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
open SourceSynthesisTypePathRoles (AnnotationFields)
variable {Symbol : Type}

mutual
/-- Every Program position has an ordinary head and certified complete rows. -/
inductive ValueFields (valid : Guard → Prop) (literal : String → Symbol) : Value Symbol Guard → Prop where
  | empty : ValueFields valid literal .empty
  | node (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth : Nat)
      (free : List Reference) (checked : ∀ row ∈ rows, EdgeFields valid literal row) :
      ValueFields valid literal (.node entry rows depth free)

/-- Each source layout retains all Type fields and recursive Program children. -/
inductive EdgeFields (valid : Guard → Prop) (literal : String → Symbol) : EdgeValue Symbol Guard → Prop where
  | annotated (edge : EdgeValue Symbol Guard) (annotation : Value Symbol Guard)
      (guard : edge.entry.key.constraint = top) (children : edge.children = [annotation])
      (typed : Annotated valid annotation) : EdgeFields valid literal edge
  | application (edge : EdgeValue Symbol Guard) (types marker function argument : Value Symbol Guard)
      (symbol : edge.entry.key.symbol = literal "app")
      (guard : edge.entry.key.constraint =
        eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      (children : edge.children = [types, marker, function, argument])
      (typesTyped : Annotated valid types) (markerTyped : Annotated valid marker)
      (functionFields : ValueFields valid literal function) (argumentFields : ValueFields valid literal argument) :
      EdgeFields valid literal edge
  | filter (edge : EdgeValue Symbol Guard) (goal candidates : Value Symbol Guard)
      (symbol : edge.entry.key.symbol = literal "filter")
      (guard : edge.entry.key.constraint = eqGuard [[[0], [1, 0]]])
      (children : edge.children = [goal, candidates]) (goalTyped : Annotated valid goal)
      (candidateFields : ValueFields valid literal candidates) : EdgeFields valid literal edge
end

/-- The recursive field certificate implies the existing strict Program role. -/
theorem ValueFields.roles {valid : Guard → Prop} {literal : String → Symbol} {value : Value Symbol Guard}
    (fields : ValueFields valid literal value) : ProgramValue literal value := by
  induction fields using ValueFields.rec (motive_2 := fun edge _ => ProgramEdge literal edge) with
  | empty => exact .empty
  | node entry rows depth free checked ih => exact .node entry rows depth free ih
  | annotated edge annotation guard children typed => exact .annotated edge annotation guard children
  | application edge types marker function argument symbol guard children typesTyped markerTyped
      functionFields argumentFields functionIH argumentIH =>
      exact .application edge types marker function argument symbol guard children functionIH argumentIH
  | filter edge goal candidates symbol guard children goalTyped candidateFields candidateIH =>
      exact .filter edge goal candidates symbol guard children candidateIH

/-- Every complete certified row has the existing strict Program role. -/
theorem EdgeFields.roles {valid : Guard → Prop} {literal : String → Symbol} {edge : EdgeValue Symbol Guard}
    (fields : EdgeFields valid literal edge) : ProgramEdge literal edge := by
  cases fields with
  | annotated edge annotation guard children typed => exact .annotated edge annotation guard children
  | application edge types marker function argument symbol guard children typesTyped markerTyped functionFields argumentFields =>
      exact .application edge types marker function argument symbol guard children functionFields.roles argumentFields.roles
  | filter edge goal candidates symbol guard children goalTyped candidateFields =>
      exact .filter edge goal candidates symbol guard children candidateFields.roles

/-- The first child of every certified row is an annotated Type. -/
theorem EdgeFields.first {valid : Guard → Prop} {literal : String → Symbol} {edge : EdgeValue Symbol Guard}
    (fields : EdgeFields valid literal edge) :
    ∀ value, edge.children[0]? = some value → Annotated valid value := by
  intro value selected
  cases fields with
  | annotated edge annotation guard children typed =>
      rw [children] at selected
      exact (Option.some.inj selected) ▸ typed
  | application edge types marker function argument symbol guard children typesTyped markerTyped functionFields argumentFields =>
      rw [children] at selected
      exact (Option.some.inj selected) ▸ typesTyped
  | filter edge goal candidates symbol guard children goalTyped candidateFields =>
      rw [children] at selected
      exact (Option.some.inj selected) ▸ goalTyped

/-- Each Program head supplies the existing annotated first-field certificate. -/
theorem ValueFields.fields {valid : Guard → Prop} {literal : String → Symbol} {value : Value Symbol Guard}
    (fields : ValueFields valid literal value) : AnnotationFields valid value := by
  cases fields with
  | empty => exact .empty
  | node entry rows depth free checked =>
      exact .node entry rows depth free (fun edge member => (checked edge member).first)

/-- Complete physical row fields transport the certificate without classifying a symbol. -/
theorem EdgeFields.congr {valid : Guard → Prop} {literal : String → Symbol} {source result : EdgeValue Symbol Guard}
    (fields : EdgeFields valid literal source)
    (symbol : result.entry.key.symbol = source.entry.key.symbol)
    (guard : result.entry.key.constraint = source.entry.key.constraint) (children : result.children = source.children) :
    EdgeFields valid literal result := by
  cases fields with
  | annotated source annotation own shape typed => exact .annotated result annotation (guard.trans own) (children.trans shape) typed
  | application source types marker function argument own constraint shape typesTyped markerTyped functionFields argumentFields =>
      exact .application result types marker function argument (symbol.trans own) (guard.trans constraint)
        (children.trans shape) typesTyped markerTyped functionFields argumentFields
  | filter source goal candidates own constraint shape goalTyped candidateFields =>
      exact .filter result goal candidates (symbol.trans own) (guard.trans constraint)
        (children.trans shape) goalTyped candidateFields

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual edge replay retains all fields of the certified request. -/
theorem makeEdge_fields (valid : Guard → Prop) (literal : String → Symbol)
    (edge : EdgeValue Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (available : Values state edge.children) (fields : EdgeFields valid literal edge) :
    EdgeFields valid literal (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) state).1 := by
  have actual := MergedPhysicalGroupEdges.makeEdge_fields state facts edge.entry.key.symbol edge.entry.key.constraint edge.children available
  exact fields.congr actual.1 actual.2.1 actual.2.2

/-- Actual node normalization retains the complete recursive row certificates. -/
theorem makeNode_fields (valid : Guard → Prop) (literal : String → Symbol)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (resident : Edges state edges) (fields : ∀ edge ∈ edges, EdgeFields valid literal edge) :
    ValueFields valid literal (run (makeNode edges) state).1 := by
  have selected : Edges state (canonicalEdges (surviving edges)) :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedFields : ∀ edge ∈ canonicalEdges (surviving edges), EdgeFields valid literal edge :=
    fun edge member => fields edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa [InternedNestedProvenance.Edges, same] using selected)
    simp only [run, readback, identifyNode]
    exact .node _ _ _ _ (by simpa [same] using selectedFields)

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem ordinary_fields (valid : Guard → Prop) (literal : String → Symbol)
    (values : List (Value Symbol Guard))
    (nodes : ∀ value ∈ values, ∃ entry rows depth free,
      value = .node entry rows depth free ∧ ∀ edge ∈ rows, EdgeFields valid literal edge) :
    ∃ edges, ordinaryEdges values = some edges ∧ ∀ edge ∈ edges, EdgeFields valid literal edge := by
  induction values with
  | nil => exact ⟨[], rfl, by intro edge member; cases member⟩
  | cons value values ih =>
      obtain ⟨entry, rows, depth, free, same, fields⟩ := nodes value List.mem_cons_self
      subst value
      obtain ⟨remaining, read, later⟩ := ih (fun value member => nodes value (List.mem_cons_of_mem _ member))
      refine ⟨rows ++ remaining, ?_, ?_⟩
      · simp only [ordinaryEdges, read, Option.map_some]
      · intro edge member
        exact (List.mem_append.mp member).elim (fields edge) (later edge)

/-- Actual source unions stay empty or ordinary and retain every Program descendant. -/
theorem makeUnion_fields (valid : Guard → Prop) (literal : String → Symbol)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : Values state values) (fields : ∀ value ∈ values, ValueFields valid literal value) :
    ValueFields valid literal (run (makeUnion values) state).1 := by
  have allAvailable : Values state (distinctNodes (values.flatMap unionMembers)) := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available source (available source included) value present
  have allNodes : ∀ value ∈ distinctNodes (values.flatMap unionMembers),
      ∃ entry rows depth free, value = .node entry rows depth free ∧ ∀ edge ∈ rows, EdgeFields valid literal edge := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    have shape := fields source included
    cases shape with
    | empty => simp only [unionMembers, List.not_mem_nil] at present
    | node entry rows depth free checked => exact ⟨entry, rows, depth, free, List.mem_singleton.mp present, checked⟩
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa only [makeUnion, normalized, run] using (ValueFields.empty (Symbol := Symbol) (valid := valid) (literal := literal))
  | cons first rest =>
      cases rest with
      | nil =>
          obtain ⟨entry, rows, depth, free, same, checked⟩ := allNodes first (by simp [normalized])
          have firstFields : ValueFields valid literal first := by
            rw [same]
            exact .node entry rows depth free checked
          simpa only [makeUnion, normalized, run] using firstFields
      | cons second tail =>
          have inputs : Values state (first :: second :: tail) :=
            fun value member => allAvailable value (by simpa only [normalized] using member)
          have nodes : ∀ value ∈ first :: second :: tail,
              ∃ entry rows depth free, value = .node entry rows depth free ∧ ∀ edge ∈ rows, EdgeFields valid literal edge := by
            simpa only [normalized] using allNodes
          obtain ⟨edges, ordinary, typed⟩ := ordinary_fields valid literal _ nodes
          have resident := ordinaryEdges_resident _ edges state facts.linked
            (fun value member => (inputs value member).resident) ordinary
          simpa only [makeUnion, normalized, ordinary] using makeNode_fields valid literal edges state facts resident typed

end MicroCFTA.SourceSynthesisHereditaryProgramFields
