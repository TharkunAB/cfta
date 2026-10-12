import MicroCFTA.InternedShallowValues

/-!
# Reachable shallow values through actual prepared execution

Binder-free source work preserves the property of its actual input values.
Canonical cache readback uses exact children and members. The theorem puts
no depth restriction on unrelated records in the same source cache.
-/
namespace MicroCFTA.InternedShallowExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedStoredSubstitution InternedStoredShallowCompletion InternedShallowValues

/-- Each actual input value satisfies the reachable shallow restriction. -/
def ShallowValues (values : List (Value Symbol Guard)) : Prop := ∀ value ∈ values, ShallowValue value

/-- Every actual child of an edge list satisfies the reachable restriction. -/
def ShallowEdges (edges : List (EdgeValue Symbol Guard)) : Prop := ShallowValues (edges.flatMap EdgeValue.children)

mutual
/-- Actual binder-free source execution preserves the reachable input restriction. -/
theorem build_shallow [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (shallow : ShallowValues environment) (free : BinderFree expression)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : build expression environment state = .done value final) : ShallowValue value := by
  cases expression with
  | empty => simp only [build, Outcome.done.injEq] at completed; rcases completed with ⟨rfl, _⟩; exact .empty
  | var index =>
      simp only [build, Outcome.done.injEq] at completed
      rcases completed with ⟨rfl, _⟩
      cases found : environment[index]? with
      | none => exact .empty
      | some value => exact shallow value (List.mem_of_getElem? found)
  | binder => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      simp only [build] at completed
      have checked := buildEdges_verified edges environment state facts inputs
      cases built : buildEdges edges environment state with
      | pending key after => simp [built, Outcome.bind] at completed
      | done values after =>
          have afterFacts : Facts after := by simpa only [built, Outcome.state] using checked.facts
          have children := buildEdges_shallow edges environment state facts inputs shallow free values after built
          simp only [built, Outcome.bind, work, Outcome.done.injEq] at completed
          exact completed.1 ▸ makeNode_shallow values after afterFacts.coherent afterFacts.linked (checked.result values after built) children
  | union members =>
      simp only [BinderFree] at free
      simp only [build] at completed
      have checked := buildMany_verified members environment state facts inputs
      cases built : buildMany members environment state with
      | pending key after => simp [built, Outcome.bind] at completed
      | done values after =>
          have afterFacts : Facts after := by simpa only [built, Outcome.state] using checked.facts
          have membersShallow := buildMany_shallow members environment state facts inputs shallow free values after built
          simp only [built, Outcome.bind, work, Outcome.done.injEq] at completed
          exact completed.1 ▸ makeUnion_shallow values after afterFacts.coherent afterFacts.cached afterFacts.linked
            (checked.result values after built) membersShallow
termination_by sizeOf expression

/-- Source child order preserves each shallow value through all earlier effects. -/
theorem buildMany_shallow [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (shallow : ShallowValues environment) (free : ManyBinderFree expressions)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard)
    (completed : buildMany expressions environment state = .done values final) : ShallowValues values := by
  cases expressions with
  | nil => simp only [buildMany, Outcome.done.injEq] at completed; rcases completed with ⟨rfl, _⟩; simp [ShallowValues]
  | cons first rest =>
      simp only [ManyBinderFree] at free
      simp only [buildMany] at completed
      have checked := build_verified first environment state facts inputs
      cases head : build first environment state with
      | pending key after => simp [head, Outcome.bind] at completed
      | done value after =>
          have afterFacts : Facts after := by simpa only [head, Outcome.state] using checked.facts
          have laterInputs : Values after environment := by
            intro value member
            simpa only [head, Outcome.state] using checked.available value (inputs value member)
          have headShallow := build_shallow first environment state facts inputs shallow free.1 value after head
          simp only [head, Outcome.bind] at completed
          cases tail : buildMany rest environment after with
          | pending key later => simp [tail] at completed
          | done remaining later =>
              have tailShallow := buildMany_shallow rest environment after afterFacts laterInputs shallow free.2 remaining later tail
              simp only [tail, Outcome.done.injEq] at completed
              rcases completed with ⟨rfl, _⟩
              intro selected member
              rcases List.mem_cons.mp member with rfl | member
              · exact headShallow
              · exact tailShallow selected member
termination_by sizeOf expressions

/-- Canonical edge readback retains the actual shallow children after all nested child effects. -/
theorem buildEdges_shallow [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (shallow : ShallowValues environment) (free : EdgesBinderFree expressions)
    (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (completed : buildEdges expressions environment state = .done edges final) : ShallowEdges edges := by
  cases expressions with
  | nil => simp only [buildEdges, Outcome.done.injEq] at completed; rcases completed with ⟨rfl, _⟩; simp [ShallowEdges, ShallowValues]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          simp only [buildEdges] at completed
          have childrenBuilt := buildMany_verified children environment state facts inputs
          cases built : buildMany children environment state with
          | pending key after => simp [built, Outcome.bind] at completed
          | done values after =>
              have childFacts : Facts after := by simpa only [built, Outcome.state] using childrenBuilt.facts
              have childValues := childrenBuilt.result values after built
              have childShallow := buildMany_shallow children environment state facts inputs shallow free.1 values after built
              let edge := run (makeEdge symbol constraint values) after
              have edgeBuilt := edge_verified symbol constraint values after childFacts childValues
              have edgeFacts : Facts edge.2 := edgeBuilt.facts
              have edgeShallow : ShallowValues edge.1.children := by
                rw [makeEdge_children symbol constraint values after childFacts.coherent childFacts.cached childValues]
                exact childShallow
              have laterInputs : Values edge.2 environment := by
                intro value member
                have intermediate : Available after value := by
                  simpa only [built, Outcome.state] using childrenBuilt.available value (inputs value member)
                exact edgeBuilt.available value intermediate
              simp only [built, Outcome.bind, work] at completed
              cases tail : buildEdges rest environment edge.2 with
              | pending key later =>
                  change (buildEdges rest environment edge.2).bind _ = _ at completed
                  simp [tail, Outcome.bind] at completed
              | done remaining later =>
                  have restShallow := buildEdges_shallow rest environment edge.2 edgeFacts laterInputs shallow free.2 remaining later tail
                  change (buildEdges rest environment edge.2).bind _ = _ at completed
                  simp only [tail, Outcome.bind, Outcome.done.injEq] at completed
                  rcases completed with ⟨rfl, _⟩
                  intro child member
                  simp only [List.flatMap_cons, List.mem_append] at member
                  exact member.elim (edgeShallow child) (restShallow child)
termination_by sizeOf expressions
end

mutual
/-- Original prepared leaves inherit the source reachable-value property. -/
theorem leaves_shallow (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (shallow : ShallowValue value) : ShallowValues (leaves value) := by
  rw [leaves.eq_def]
  split
  · intro leaf member
    have same : leaf = value := by simpa using member
    exact same ▸ shallow
  · cases shallow with
    | empty =>
        intro leaf member
        have same : leaf = .empty := by simpa using member
        exact same ▸ ShallowValue.empty
    | reference name =>
        intro leaf member
        have same : leaf = .reference name := by simpa using member
        exact same ▸ ShallowValue.reference name
    | node entry edges depth free children =>
        exact edgeLeaves_shallow edges state coherent (fun value member => available.children value member) children
    | union entry members depth free children =>
        exact manyLeaves_shallow members state coherent (fun value member => available.children value member) children
    | mu entry body depth ordinary zero =>
        have bodyAvailable : Available state body := available.children body (by simp [InternedProbeProvenance.children])
        exact leaves_shallow body state coherent bodyAvailable (depth_zero body state coherent bodyAvailable zero)
termination_by sizeOf value

/-- Ordered source child leaves retain the same reachable restriction. -/
theorem manyLeaves_shallow (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (shallow : ShallowValues values) : ShallowValues (manyLeaves values) := by
  cases values with
  | nil => simp [ShallowValues, manyLeaves]
  | cons first rest =>
      intro leaf member
      simp only [manyLeaves] at member
      rcases List.mem_append.mp member with head | tail
      · exact leaves_shallow first state coherent (available first (by simp)) (shallow first (by simp)) leaf head
      · exact manyLeaves_shallow rest state coherent (fun value member => available value (by simp [member]))
          (fun value member => shallow value (by simp [member])) leaf tail
termination_by sizeOf values

/-- Actual source edge payloads contain only the prepared leaves of their original children. -/
theorem edgeLeaves_shallow (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (shallow : ShallowEdges edges) : ShallowValues (edgeLeaves edges) := by
  cases edges with
  | nil => simp [ShallowValues, edgeLeaves]
  | cons first rest =>
      cases first with
      | mk entry children =>
          intro leaf member
          simp only [edgeLeaves] at member
          rcases List.mem_append.mp member with head | tail
          · exact manyLeaves_shallow children state coherent
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun value member => shallow value (by simp [EdgeValue.children, member])) leaf head
          · exact edgeLeaves_shallow rest state coherent
              (fun value member => available value (by simp [EdgeValue.children, member]))
              (fun value member => shallow value (by simp [EdgeValue.children, member])) leaf tail
termination_by sizeOf edges
end

/-- Prepared inputs inherit shallowness from original records and actual replacements. -/
theorem inputs_shallow (value : Value Symbol Guard) (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (shallow : ShallowValue value)
    (replacements : ∀ name replacement, environment name = some replacement → ShallowValue replacement) :
    ShallowValues ((leaves value).map (input environment)) := by
  intro selected member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have source := leaves_shallow value state coherent available shallow original present
  cases original with
  | empty | node | union | mu => exact source
  | reference name =>
      cases found : environment name with
      | none => simpa [input, found] using source
      | some replacement => simpa [input, found] using replacements name replacement found

/-- Actual shallow unfolding preserves the queried value's reachable
restriction in an arbitrary coherent cache, with no global depth bound. -/
theorem unfold_shallow [DecidableEq (EdgeKey Symbol Guard)] (original : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state original)
    (shallow : ShallowValue original) (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : InternedStoredSubstitution.unfold original state = .done value final) : ShallowValue value := by
  cases original with
  | empty | reference | node | union => cases completed; exact shallow
  | mu entry body depth ordinary =>
      have zero := mu_zero entry body depth ordinary shallow
      have bodyAvailable : Available state body := available.children body (by simp [InternedProbeProvenance.children])
      have bodyShallow := depth_zero body state facts.coherent bodyAvailable zero
      let environment : Environment Symbol Guard := fun name =>
        if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
      have replacementAvailable : Replacements state environment := by
        intro name replacement found
        dsimp only [environment] at found
        split at found
        · cases found; exact available
        · contradiction
      have replacementShallow : ∀ name replacement, environment name = some replacement → ShallowValue replacement := by
        intro name replacement found
        dsimp only [environment] at found
        split at found
        · cases found; exact shallow
        · contradiction
      exact build_shallow _ _ state facts
        (inputs_available body environment state bodyAvailable replacementAvailable)
        (inputs_shallow body environment state facts.coherent bodyAvailable bodyShallow replacementShallow)
        (encode_zero (leaves body) [] body state facts.coherent bodyAvailable zero) value final completed

end MicroCFTA.InternedShallowExecution
