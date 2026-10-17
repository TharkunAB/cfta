import MicroCFTA.SourceCurrentConstrainedCapConstruction
import MicroCFTA.SourceCurrentConstrainedCapNativeScope
import MicroCFTA.InternedStoredSubstitutionBindings
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.SourceEqualityRequiredCache

/-!
# Actual stored substitution at a finite constraint depth

The syntax checks each lexical capture only where the source plan uses it.
A source Mu body is hereditary. Its reconstruction uses the causal Mu store.
Unrelated constrained captures remain permitted. The complete endpoint derives
its own actual return from the initial complete semantic cache.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapStoredSubstitution
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution InternedStoredSubstitutionBindings
open InternedBinderProtocol (Reference)
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapConstruction (Typed ManyTyped EdgesTyped)
open SourceCurrentHereditaryConstruction (MuStored Checked)

/-- A hereditary replacement retains every finite constraint-depth bound. -/
theorem input_cap (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (bounded : Cap valid depth value)
    (replacements : ∀ name result, environment name = some result → Annotated valid result) :
    Cap valid depth (input environment value) := by
  cases value with
  | empty | node | union | mu => exact bounded
  | reference name =>
      cases found : environment name with
      | none => simpa only [input, found, Option.getD_none] using bounded
      | some result => simpa only [input, found, Option.getD_some] using Cap.plain depth (replacements name result found)

private theorem edge_guard {valid : Guard → Prop} {depth : Nat} {edge : EdgeValue Symbol Guard}
    (bounded : SourceCurrentConstrainedCap.Edge valid depth edge) (zero : depth = 0) : valid edge.entry.key.constraint := by
  subst depth
  exact bounded.1

private theorem edge_child {valid : Guard → Prop} {depth : Nat} {edge : EdgeValue Symbol Guard}
    (bounded : SourceCurrentConstrainedCap.Edge valid depth edge) (value : Value Symbol Guard) (member : value ∈ edge.children) :
    Cap valid (depth - 1) value := by
  cases depth with
  | zero => exact .plain 0 (bounded.2 value member)
  | succ depth => exact bounded value member

mutual
/-- The actual stored plan uses only original finite-cap captures and hereditary replacements. -/
theorem encode_typed (valid : Guard → Prop) (depth : Nat) (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Available state value) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (length : localValues.length = locals.length) (localAnnotations : ∀ value ∈ localValues, Annotated valid value)
    (replacements : ∀ name result, environment name = some result → Annotated valid result)
    (bounded : Cap valid depth value) :
    Typed valid depth (encode context locals value) (localValues ++ context.map (input environment)) := by
  rw [encode.eq_def]
  split
  · rename_i closed
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp [closed])
    simp only [Typed, global_lookup context locals localValues value environment state coherent contextAvailable member length,
      Option.getD_some]
    exact input_cap valid depth value environment bounded replacements
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened, Bool.false_eq_true, ↓reduceIte] at covered
    cases value with
    | empty => simp only [Typed]
    | reference name =>
        cases found : locals.findIdx? (· == name) with
        | some index =>
            have bound : index < localValues.length := by
              rw [length]
              exact (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
            simp only [found, Typed, List.getElem?_append_left bound]
            cases selected : localValues[index]? with
            | none => exact .plain depth .empty
            | some value => exact .plain depth (localAnnotations value (List.mem_of_getElem? selected))
        | none =>
            have member := covered (.reference name) (by simp)
            simp only [found, Typed,
              global_lookup context locals localValues (.reference name) environment state coherent contextAvailable member length,
              Option.getD_some]
            exact input_cap valid depth (.reference name) environment bounded replacements
    | node entry edges level free =>
        simpa only [Typed] using encodeEdges_typed valid depth context locals localValues edges environment state coherent contextAvailable
          (fun child member => available.children child member) covered length localAnnotations replacements
          (fun edge member => SourceCurrentConstrainedCap.node_edge bounded edge member)
    | union entry members level free =>
        simpa only [Typed] using encodeMany_typed valid depth context locals localValues members environment state coherent contextAvailable
          (fun child member => available.children child member) covered length localAnnotations replacements
          (fun child member => SourceCurrentConstrainedCap.union_member bounded child member)
    | mu entry body level ordinary =>
        have annotated := SourceCurrentConstrainedCapNativeScope.mu_annotated bounded
        cases annotated with
        | mu _ _ _ _ bodyAnnotated =>
            simp only [Typed]
            intro name
            exact encode_typed valid 0 context (.interned entry.identity :: locals) (.reference name :: localValues)
              body environment state coherent contextAvailable
              (available.children body (by simp [InternedProbeProvenance.children])) covered (by simp [length])
              (by intro value member; rcases List.mem_cons.mp member with same | later
                  · subst value; exact .reference name
                  · exact localAnnotations value later)
              replacements (.plain 0 bodyAnnotated)
termination_by sizeOf value

/-- Ordered source child plans retain their original selective lexical checks. -/
theorem encodeMany_typed (valid : Guard → Prop) (depth : Nat) (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (values : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (length : localValues.length = locals.length) (localAnnotations : ∀ value ∈ localValues, Annotated valid value)
    (replacements : ∀ name result, environment name = some result → Annotated valid result)
    (bounded : ∀ value ∈ values, Cap valid depth value) :
    ManyTyped valid depth (encodeMany context locals values) (localValues ++ context.map (input environment)) := by
  cases values with
  | nil => simp only [encodeMany, ManyTyped]
  | cons first rest =>
      simp only [encodeMany, ManyTyped]
      exact ⟨encode_typed valid depth context locals localValues first environment state coherent contextAvailable
        (available first List.mem_cons_self) (fun leaf member => covered leaf (by simp [manyLeaves, member])) length
        localAnnotations replacements (bounded first List.mem_cons_self),
        encodeMany_typed valid depth context locals localValues rest environment state coherent contextAvailable
          (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun leaf member => covered leaf (by simp [manyLeaves, member])) length localAnnotations replacements
          (fun value member => bounded value (List.mem_cons_of_mem _ member))⟩
termination_by sizeOf values

/-- Original row guards are checked only at zero and original children one depth below. -/
theorem encodeEdges_typed (valid : Guard → Prop) (depth : Nat) (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard)) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context)
    (length : localValues.length = locals.length) (localAnnotations : ∀ value ∈ localValues, Annotated valid value)
    (replacements : ∀ name result, environment name = some result → Annotated valid result)
    (bounded : ∀ edge ∈ edges, SourceCurrentConstrainedCap.Edge valid depth edge) :
    EdgesTyped valid depth (encodeEdges context locals edges) (localValues ++ context.map (input environment)) := by
  cases edges with
  | nil => simp only [encodeEdges, EdgesTyped]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [encodeEdges, EdgesTyped]
          refine ⟨edge_guard (bounded (.mk entry children) List.mem_cons_self), ?_, ?_⟩
          · exact encodeMany_typed valid (depth - 1) context locals localValues children environment state coherent contextAvailable
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun leaf member => covered leaf (by simp [edgeLeaves, member])) length localAnnotations replacements
              (fun value member => edge_child (bounded (.mk entry children) List.mem_cons_self) value member)
          · exact encodeEdges_typed valid depth context locals localValues rest environment state coherent contextAvailable
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun leaf member => covered leaf (by simp [edgeLeaves, member])) length localAnnotations replacements
              (fun edge member => bounded edge (List.mem_cons_of_mem _ member))
termination_by sizeOf edges
end

/-- The actual executor retains the causal Mu store and checks every returned finite-cap value. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (available : Available state value) (bounded : Cap valid depth value)
    (replacements : Replacements state environment)
    (replacementAnnotations : ∀ name result, environment name = some result → Annotated valid result)
    (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryStoredSubstitution.execute value environment state) (Cap valid depth) := by
  have typed := encode_typed valid depth (leaves value) [] [] value environment state facts.coherent
    (leaves_available value state available) available (fun _ member => member) rfl
    (by intro _ member; cases member) replacementAnnotations bounded
  exact SourceCurrentConstrainedCapConstruction.build valid depth _ _ state facts
    (inputs_available value environment state available replacements) typed stored

/-- Initial complete semantic data constructs its own same-depth stored-substitution return. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready state)
    (available : Available state value) (bounded : Cap valid depth value)
    (replacements : Replacements state environment)
    (replacementAnnotations : ∀ name result, environment name = some result → Annotated valid result)
    (stored : MuStored valid state) :
    ∃ result after, InternedFreshOrdinaryStoredSubstitution.execute value environment state = .done result after ∧
      Cap valid depth result ∧ MuStored valid after ∧ Available after result ∧
      SourceEqualityRequiredCache.Ready after ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued := by
  obtain ⟨result, after, done, context, heap, covered, output, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.execute_complete_decoded value environment state ready.semantic.1 available
      replacements ready.semantic.2 ready.covered
  have checked := execute valid depth value environment state ready.semantic.1.normal.facts available bounded replacements
    replacementAnnotations stored
  have sourceContext : InternedFreshOrdinaryContext.Context state ((leaves value).map (input environment)) :=
    ⟨ready.semantic.1.normal, inputs_available value environment state available replacements,
      ready.semantic.1.profiles, ready.semantic.1.freeNames⟩
  have depthRetained := InternedOpenDepthExecution.build_depth (encode (leaves value) [] value) _ state
    sourceContext ready.semantic.2 ready.depth
  have afterDepth : InternedOpenDepthReadback.Heap after := by
    have retained := depthRetained.heap
    change InternedOpenDepthReadback.Heap (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state at retained
    simpa only [done, Outcome.state] using retained
  exact ⟨result, after, done, checked.result result after done, by simpa only [done, Outcome.state] using checked.stored,
    output, ⟨⟨context, heap⟩, covered, afterDepth⟩, growth, history⟩

end MicroCFTA.SourceCurrentConstrainedCapStoredSubstitution
