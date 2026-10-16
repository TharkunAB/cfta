import MicroCFTA.SourceCurrentHereditaryConstructors
import MicroCFTA.SourceCurrentHereditaryUnconstrained
import MicroCFTA.InternedFreshOrdinaryReadback
import MicroCFTA.SourceEqualityAnnotationStoredSyntax

/-!
# Local annotations through actual stored-body construction

A conditional certificate belongs to each completed Mu cache entry. It links
that body's annotations to its two complete probes. It permits unrelated
constrained records. Actual allowed construction produces the certificate
for each new body before first-writer readback. Physical Facts alone do not
supply this representation invariant for arbitrary earlier Mu records.
-/
namespace MicroCFTA.SourceCurrentHereditaryConstruction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshProbeKeys InternedFreshOrdinaryConstruction
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationConstruction
open SourceCurrentHereditaryConstructors (Edge)

/-- Earlier Mu bodies inherit a predicate when both exact stored probes have that predicate. -/
def MuStored (valid : Guard → Prop) (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Annotated valid depth → Annotated valid ordinary → Annotated valid body

/-- Empty caches have no completed Mu obligation. -/
theorem MuStored.empty (valid : Guard → Prop) : MuStored valid (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary absent
  cases absent

/-- An operation with no new Mu preserves the conditional earlier-body certificates. -/
theorem MuStored.preserve {valid : Guard → Prop} {before after : State Symbol Guard}
    (stored : MuStored valid before) (old : InternedShallowHeap.NoNewMu before after) : MuStored valid after := by
  intro key entry body depth ordinary present
  exact stored key entry body depth ordinary (old key entry body depth ordinary present)

/-- A node constructor changes no completed Mu payload. -/
theorem MuStored.makeNode [DecidableEq (EdgeKey Symbol Guard)] {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (edges : List (EdgeValue Symbol Guard)) :
    MuStored valid (run (InternedConstructorTemplates.makeNode edges) state).2 :=
  stored.preserve (InternedShallowHeap.makeNode_noNewMu edges state)

/-- An edge constructor changes no completed Mu payload. -/
theorem MuStored.makeEdge [DecidableEq (EdgeKey Symbol Guard)] {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) :
    MuStored valid (run (InternedConstructorTemplates.makeEdge symbol guard values) state).2 := stored

/-- A union constructor changes no completed Mu payload. -/
theorem MuStored.makeUnion [DecidableEq (EdgeKey Symbol Guard)] {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (values : List (Value Symbol Guard)) :
    MuStored valid (run (InternedConstructorTemplates.makeUnion values) state).2 :=
  stored.preserve (InternedShallowHeap.makeUnion_noNewMu values state)

/-- Reserving an identity changes no earlier complete Mu record. -/
theorem MuStored.reserve {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (key : NodeKey) :
    MuStored valid {state with nodes := (Cache.intern state.nodes key).2} := stored

/-- Smart cleanup selects the stored body, empty, or the same annotated Mu. -/
theorem finish_annotated (valid : Guard → Prop) (smart : Bool) (value : Value Symbol Guard)
    (annotated : Annotated valid value) : Annotated valid (finish smart value) := by
  cases smart with
  | false => exact annotated
  | true =>
      cases annotated with
      | empty => exact .empty
      | reference name => exact .reference name
      | node entry edges depth free guards children => exact .node entry edges depth free guards children
      | union entry members depth free children => exact .union entry members depth free children
      | mu entry body depth ordinary annotated =>
          simp only [finish, ↓reduceIte, cleanup]
          split
          · exact annotated
          · split
            · exact .empty
            · exact .mu _ _ _ _ annotated

/-- A certificate describes actual cache retention and each actual successful returned value. -/
structure Checked (valid : Guard → Prop) (outcome : Outcome Symbol Guard A) (post : A → Prop) : Prop where
  /-- The exact stopping cache retains conditional Mu certificates. -/
  stored : MuStored valid outcome.state
  /-- Each literal successful result satisfies its local postcondition. -/
  result : ∀ value after, outcome = .done value after → post value

private theorem checked_pure (valid : Guard → Prop) (value : A) (state : State Symbol Guard) (post : A → Prop)
    (stored : MuStored valid state) (result : post value) : Checked valid (.done value state) post :=
  ⟨stored, fun _ _ same => by cases same; exact result⟩

private theorem checked_bind {valid : Guard → Prop} {outcome : Outcome Symbol Guard A} {post : A → Prop}
    {next : A → State Symbol Guard → Outcome Symbol Guard B} {last : B → Prop}
    (first : Checked valid outcome post)
    (later : ∀ value after, outcome = .done value after → post value → MuStored valid after → Checked valid (next value after) last) :
    Checked valid (outcome.bind next) last := by
  cases outcome with
  | pending key after => exact ⟨first.stored, by intro _ _ impossible; cases impossible⟩
  | done value after => exact later value after rfl (first.result value after rfl) first.stored

/-- Bare self filtering retains local annotations and conditional Mu certificates. -/
theorem filter_checked [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (name : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state) (available : Available state value)
    (annotated : Annotated valid value) (stored : MuStored valid state) :
    Checked valid (work (withoutSelfReference name value) state) (Annotated valid) := by
  have kept : MuStored valid (run (withoutSelfReference name value) state).2 :=
    stored.preserve (InternedStoredMuOrigins.filter_noNewMu name value state)
  refine ⟨kept, ?_⟩
  intro result after done
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj done
  cases annotated with
  | empty => exact .empty
  | reference name => exact .reference name
  | node entry edges depth free guards children => exact .node entry edges depth free guards children
  | mu entry body depth ordinary annotated => exact .mu entry body depth ordinary annotated
  | union entry members depth free children =>
      unfold withoutSelfReference
      split
      · apply SourceCurrentHereditaryConstructors.makeUnion valid _ state facts
        · intro value member
          exact available.children value (List.mem_filter.mp member).1
        · intro value member
          exact children value (List.mem_filter.mp member).1
      · exact .union entry members depth free children

private theorem complete_checked (valid : Guard → Prop) (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (annotated : Annotated valid body) (depthAnnotated : Annotated valid depth) (ordinaryAnnotated : Annotated valid ordinary)
    (stored : MuStored valid state) :
    Checked valid (InternedNestedRequestFacts.complete smart entry body depth ordinary state) (Annotated valid) := by
  have retained : MuStored valid
      {state with nodeRecords := keepFirst state.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary)} := by
    intro key own ownBody ownDepth ownOrdinary present
    rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
        (.mu own ownBody ownDepth ownOrdinary) present with old | ⟨_, same⟩
    · exact stored key own ownBody ownDepth ownOrdinary old
    · cases same
      exact fun _ _ => annotated
  refine ⟨retained, ?_⟩
  intro result after done
  obtain ⟨winner, present⟩ := keepFirst_present state.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary)
  simp only [InternedNestedRequestFacts.complete, present, Option.getD_some] at done
  cases done
  apply finish_annotated
  rcases record_cases state.nodeRecords (muKey depth ordinary) (muKey depth ordinary) (.mu entry body depth ordinary)
      winner present with old | ⟨_, same⟩
  · obtain ⟨own, ownBody, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary winner state facts depthAvailable ordinaryAvailable old
    exact .mu _ _ _ _ (stored _ _ _ _ _ old depthAnnotated ordinaryAnnotated)
  · cases same
    exact .mu _ _ _ _ annotated

private theorem request_checked [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (smart : Bool) (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (depthAnnotated : Annotated valid depth) (ordinaryAnnotated : Annotated valid ordinary)
    (stored : MuStored valid state)
    (recurse : ∀ name current, Facts current → Values current environment → Available current (.reference name) →
      MuStored valid current → Checked valid (InternedFreshOrdinaryFacts.callback body environment name current) (Annotated valid)) :
    Checked valid (request smart depth ordinary (InternedFreshOrdinaryFacts.callback body environment) state) (Annotated valid) := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => exact ⟨by simpa only [request, installed, present, Outcome.state] using stored,
          by intro _ _ impossible; simp only [request, installed, present] at impossible; cases impossible⟩
      | some value =>
          obtain ⟨own, ownBody, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
          simpa only [request, installed, present] using checked_pure valid _ state (Annotated valid) stored
            (finish_annotated valid smart _ (.mu _ _ _ _ (stored _ _ _ _ _ present depthAnnotated ordinaryAnnotated)))
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have growth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends state.nodes key facts.coherent.valid.2
      have allocatedInputs : Values allocated environment := fun value member =>
        (inputs value member).grows _ _ growth history
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (InternedConstructionProvenance.reserve_available key state facts.coherent facts.cached).2
      have physical := InternedFreshOrdinaryFacts.callback_verified body environment (.interned entry.1.identity)
        allocated (reserve_facts key state facts) (by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact allocatedInputs value member)
      have actual := recurse (.interned entry.1.identity) allocated (reserve_facts key state facts)
        allocatedInputs argument (stored.reserve key)
      simp only [request, installed]
      change Checked valid ((InternedFreshOrdinaryFacts.callback body environment (.interned entry.1.identity) allocated).bind
        (fun value after => InternedNestedRequestFacts.complete smart entry.1 value depth ordinary after)) (Annotated valid)
      apply checked_bind actual
      intro value after done annotated kept
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using physical.facts
      have afterDepth : Available after depth := by
        simpa only [done, Outcome.state] using physical.available depth (depthAvailable.grows _ _ growth history)
      have afterOrdinary : Available after ordinary := by
        simpa only [done, Outcome.state] using physical.available ordinary (ordinaryAvailable.grows _ _ growth history)
      exact complete_checked valid smart entry.1 value depth ordinary after afterFacts afterDepth afterOrdinary
        annotated depthAnnotated ordinaryAnnotated kept

mutual
/-- Actual allowed construction derives local result annotations and retains the causal Mu store. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (allowed : Allowed valid expression)
    (annotated : ∀ value ∈ environment, Annotated valid value) (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryConstruction.build expression environment state) (Annotated valid) := by
  cases expression with
  | empty => simpa only [InternedFreshOrdinaryConstruction.build] using
      checked_pure valid (.empty : Value Symbol Guard) state (Annotated valid) stored Annotated.empty
  | var index =>
      cases found : environment[index]? with
      | none => simpa only [InternedFreshOrdinaryConstruction.build, found, Option.getD_none] using
          checked_pure valid (.empty : Value Symbol Guard) state _ stored Annotated.empty
      | some value => simpa only [InternedFreshOrdinaryConstruction.build, found, Option.getD_some] using
          checked_pure valid value state _ stored (annotated value (List.mem_of_getElem? found))
  | node edges =>
      simp only [Allowed] at allowed
      have physical := InternedFreshOrdinaryFacts.buildEdges_verified edges environment state facts inputs
      rw [InternedFreshOrdinaryConstruction.build]
      apply checked_bind (buildEdges valid edges environment state facts inputs allowed annotated stored)
      intro values after done localRows kept
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using physical.facts
      have resident := physical.result values after done
      exact ⟨kept.makeNode values, fun result final returned => by
        obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
        exact SourceCurrentHereditaryConstructors.makeNode valid values after afterFacts.coherent afterFacts.linked resident localRows⟩
  | union members =>
      simp only [Allowed] at allowed
      have physical := InternedFreshOrdinaryFacts.buildMany_verified members environment state facts inputs
      rw [InternedFreshOrdinaryConstruction.build]
      apply checked_bind (buildMany valid members environment state facts inputs allowed annotated stored)
      intro values after done localValues kept
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using physical.facts
      have available := physical.result values after done
      exact ⟨kept.makeUnion values, fun result final returned => by
        obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
        exact SourceCurrentHereditaryConstructors.makeUnion valid values after afterFacts available localValues⟩
  | binder smart body =>
      simp only [Allowed] at allowed
      have calls (name : Reference) (current : State Symbol Guard) (currentFacts : Facts current)
          (currentInputs : Values current environment) (argument : Available current (.reference name))
          (kept : MuStored valid current) :
          Checked valid (InternedFreshOrdinaryFacts.callback body environment name current) (Annotated valid) := by
        have extended : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentInputs value member
        have localAnnotations : ∀ value ∈ .reference name :: environment, Annotated valid value := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact .reference _
          · exact annotated value member
        have physical := InternedFreshOrdinaryFacts.build_verified body _ current currentFacts extended
        unfold InternedFreshOrdinaryFacts.callback
        apply checked_bind (build valid body _ current currentFacts extended allowed localAnnotations kept)
        intro value after done resultAnnotated afterStored
        have afterFacts : Facts after := by simpa only [done, Outcome.state] using physical.facts
        exact filter_checked valid name value after afterFacts (physical.result value after done) resultAnnotated afterStored
      have depthPhysical := InternedFreshOrdinaryFacts.callback_verified body environment .depth state facts
        (by intro value member; rcases List.mem_cons.mp member with rfl | member
            · exact depth_available state
            · exact inputs value member)
      rw [InternedFreshOrdinaryConstruction.build]
      change Checked valid ((InternedFreshOrdinaryFacts.callback body environment .depth state).bind fun depth middle =>
        (InternedFreshOrdinaryFacts.callback body environment (.uninterned (ordinaryLevel depth)) middle).bind
          fun ordinary cut => request smart depth ordinary (InternedFreshOrdinaryFacts.callback body environment) cut) (Annotated valid)
      apply checked_bind (calls .depth state facts inputs (depth_available state) stored)
      intro depth middle depthDone depthAnnotated depthStored
      have middleFacts : Facts middle := by simpa only [depthDone, Outcome.state] using depthPhysical.facts
      have middleInputs : Values middle environment := fun value member => by
        simpa only [depthDone, Outcome.state] using depthPhysical.available value (inputs value member)
      have depthAvailable := depthPhysical.result depth middle depthDone
      have ordinaryPhysical := InternedFreshOrdinaryFacts.callback_verified body environment (.uninterned (ordinaryLevel depth))
        middle middleFacts (by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact ordinary_available middle _
          · exact middleInputs value member)
      apply checked_bind (calls (.uninterned (ordinaryLevel depth)) middle middleFacts middleInputs
        (ordinary_available middle _) depthStored)
      intro ordinary cut ordinaryDone ordinaryAnnotated ordinaryStored
      have cutFacts : Facts cut := by simpa only [ordinaryDone, Outcome.state] using ordinaryPhysical.facts
      have cutInputs : Values cut environment := fun value member => by
        simpa only [ordinaryDone, Outcome.state] using ordinaryPhysical.available value (middleInputs value member)
      have cutDepth : Available cut depth := by
        simpa only [ordinaryDone, Outcome.state] using ordinaryPhysical.available depth depthAvailable
      exact request_checked valid smart body environment depth ordinary cut cutFacts cutInputs cutDepth
        (ordinaryPhysical.result ordinary cut ordinaryDone) depthAnnotated ordinaryAnnotated ordinaryStored calls
termination_by sizeOf expression

/-- Actual ordered child construction retains one local annotation at each returned position. -/
theorem buildMany [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (allowed : ManyAllowed valid expressions)
    (annotated : ∀ value ∈ environment, Annotated valid value) (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryConstruction.buildMany expressions environment state)
      (fun values => ∀ value ∈ values, Annotated valid value) := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildMany] using
      (checked_pure valid ([] : List (Value Symbol Guard)) state (fun values => ∀ value ∈ values, Annotated valid value)
        stored (by intro value member; cases member))
  | cons first rest =>
      simp only [ManyAllowed] at allowed
      have physical := InternedFreshOrdinaryFacts.build_verified first environment state facts inputs
      rw [InternedFreshOrdinaryConstruction.buildMany]
      apply checked_bind (build valid first environment state facts inputs allowed.1 annotated stored)
      intro value middle done valueAnnotated middleStored
      have middleFacts : Facts middle := by simpa only [done, Outcome.state] using physical.facts
      have middleInputs : Values middle environment := fun child member => by
        simpa only [done, Outcome.state] using physical.available child (inputs child member)
      apply checked_bind (buildMany valid rest environment middle middleFacts middleInputs allowed.2 annotated middleStored)
      intro values after returned valuesAnnotated afterStored
      exact checked_pure valid (value :: values) after _ afterStored (by
        intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact valueAnnotated
        · exact valuesAnnotated child member)
termination_by sizeOf expressions

/-- Actual edge construction checks its own guard after its ordered children complete. -/
theorem buildEdges [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (allowed : EdgesAllowed valid expressions)
    (annotated : ∀ value ∈ environment, Annotated valid value) (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryConstruction.buildEdges expressions environment state)
      (fun edges => ∀ edge ∈ edges, Edge valid edge) := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildEdges] using
      (checked_pure valid ([] : List (EdgeValue Symbol Guard)) state (fun edges => ∀ edge ∈ edges, Edge valid edge)
        stored (by intro edge member; cases member))
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [EdgesAllowed] at allowed
          have physical := InternedFreshOrdinaryFacts.buildMany_verified children environment state facts inputs
          rw [InternedFreshOrdinaryConstruction.buildEdges]
          apply checked_bind (buildMany valid children environment state facts inputs allowed.2.1 annotated stored)
          intro values middle done valuesAnnotated middleStored
          have middleFacts : Facts middle := by simpa only [done, Outcome.state] using physical.facts
          have available := physical.result values middle done
          have edgePhysical := InternedNestedFacts.edge_verified symbol guard values middle middleFacts available
          have edgeChecked : Checked valid (work (InternedConstructorTemplates.makeEdge symbol guard values) middle) (Edge valid) :=
            ⟨middleStored.makeEdge symbol guard values, fun edge after returned => by
              obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
              exact SourceCurrentHereditaryConstructors.makeEdge valid symbol guard values middle
                middleFacts.coherent middleFacts.cached available allowed.1 valuesAnnotated⟩
          apply checked_bind edgeChecked
          intro edge cut built edgeAnnotated edgeStored
          have cutFacts : Facts cut := by simpa only [built, Outcome.state] using edgePhysical.facts
          have cutInputs : Values cut environment := fun value member => by
            have earlier : Available middle value := by
              simpa only [done, Outcome.state] using physical.available value (inputs value member)
            simpa only [built, Outcome.state] using edgePhysical.available value earlier
          apply checked_bind (buildEdges valid rest environment cut cutFacts cutInputs allowed.2.2 annotated edgeStored)
          intro edges after returned edgesAnnotated afterStored
          exact checked_pure valid (edge :: edges) after _ afterStored (by
            intro chosen member
            rcases List.mem_cons.mp member with rfl | member
            · exact edgeAnnotated
            · exact edgesAnnotated chosen member)
termination_by sizeOf expressions
end

private theorem many_leaves (valid : Guard → Prop) (values : List (Value Symbol Guard))
    (annotated : ∀ value ∈ values, ∀ leaf ∈ InternedStoredSubstitution.leaves value, Annotated valid leaf) :
    ∀ leaf ∈ InternedStoredSubstitution.manyLeaves values, Annotated valid leaf := by
  induction values with
  | nil => intro leaf member; cases member
  | cons first rest ih =>
      intro leaf member
      rw [InternedStoredSubstitution.manyLeaves] at member
      rcases List.mem_append.mp member with own | later
      · exact annotated first List.mem_cons_self leaf own
      · exact ih (fun value member => annotated value (List.mem_cons_of_mem _ member)) leaf later

private theorem edge_leaves (valid : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (annotated : ∀ value ∈ edges.flatMap EdgeValue.children, ∀ leaf ∈ InternedStoredSubstitution.leaves value,
      Annotated valid leaf) :
    ∀ leaf ∈ InternedStoredSubstitution.edgeLeaves edges, Annotated valid leaf := by
  induction edges with
  | nil => intro leaf member; cases member
  | cons edge rest ih =>
      cases edge with
      | mk entry children =>
          intro leaf member
          rw [InternedStoredSubstitution.edgeLeaves] at member
          rcases List.mem_append.mp member with own | later
          · exact many_leaves valid children (fun value member => annotated value
              (List.mem_flatMap.mpr ⟨.mk entry children, List.mem_cons_self, member⟩)) leaf own
          · exact ih (fun value member => annotated value (List.mem_flatMap.mpr (by
              obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
              exact ⟨edge, List.mem_cons_of_mem _ present, inside⟩))) leaf later

/-- Prepared captures retain only annotations of the actual supplied source record. -/
theorem leaves_annotated (valid : Guard → Prop) (value : Value Symbol Guard) (annotated : Annotated valid value) :
    ∀ leaf ∈ InternedStoredSubstitution.leaves value, Annotated valid leaf := by
  induction annotated with
  | empty =>
      simp only [InternedStoredSubstitution.leaves.eq_def, Value.free, List.isEmpty_nil, ↓reduceIte]
      intro leaf member
      exact (List.mem_singleton.mp member) ▸ Annotated.empty
  | reference name =>
      simp only [InternedStoredSubstitution.leaves.eq_def, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      intro leaf member
      exact (List.mem_singleton.mp member) ▸ Annotated.reference name
  | node entry edges depth free guards children ih =>
      rw [InternedStoredSubstitution.leaves.eq_def]
      split
      · intro leaf member
        exact (List.mem_singleton.mp member) ▸ Annotated.node entry edges depth free guards children
      · exact edge_leaves valid edges ih
  | union entry members depth free children ih =>
      rw [InternedStoredSubstitution.leaves.eq_def]
      split
      · intro leaf member
        exact (List.mem_singleton.mp member) ▸ Annotated.union entry members depth free children
      · exact many_leaves valid members ih
  | mu entry body depth ordinary annotated ih =>
      rw [InternedStoredSubstitution.leaves.eq_def]
      split
      · intro leaf member
        exact (List.mem_singleton.mp member) ▸ Annotated.mu entry body depth ordinary annotated
      · exact ih

/-- Actual substitution captures retain source annotations or the supplied annotated replacement. -/
theorem inputs_annotated (valid : Guard → Prop) (value : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (annotated : Annotated valid value)
    (replacements : ∀ name replacement, environment name = some replacement → Annotated valid replacement) :
    ∀ input ∈ (InternedStoredSubstitution.leaves value).map (InternedStoredSubstitution.input environment), Annotated valid input := by
  intro input member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have source := leaves_annotated valid value annotated original present
  cases original with
  | empty | node | union | mu => exact source
  | reference name =>
      cases found : environment name with
      | none => simpa only [InternedStoredSubstitution.input, found, Option.getD_none] using source
      | some replacement => simpa only [InternedStoredSubstitution.input, found, Option.getD_some] using replacements name replacement found

/-- Actual repaired stored substitution derives the local result and its conditional Mu cache. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (value : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) (annotated : Annotated valid value)
    (replacements : InternedStoredSubstitution.Replacements state environment)
    (replacementAnnotations : ∀ name replacement, environment name = some replacement → Annotated valid replacement)
    (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryStoredSubstitution.execute value environment state) (Annotated valid) :=
  build valid _ _ state facts (InternedStoredSubstitution.inputs_available value environment state available replacements)
    (SourceEqualityAnnotationStoredSyntax.encode_allowed valid value annotated _ [])
    (inputs_annotated valid value environment annotated replacementAnnotations) stored

/-- Actual outer unfolding substitutes the same annotated Mu without constraining unrelated records. -/
theorem unfold [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value)
    (annotated : Annotated valid value) (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryStoredSubstitution.unfold value state) (Annotated valid) := by
  cases value with
  | empty | reference | node | union => exact checked_pure valid _ state _ stored annotated
  | mu entry body depth ordinary =>
      apply execute valid body _ state facts
        (available.children body (by simp [InternedProbeProvenance.children]))
        (SourceCurrentHereditaryUnconstrained.mu_body annotated)
      · intro name replacement found
        split at found
        · cases found
          exact available
        · cases found
      · intro name replacement found
        split at found
        · cases found
          exact annotated
        · cases found
      · exact stored

/-- Actual optional binding derives a local annotated result and its conditional Mu store. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (key : Nat × Nat)
    (body : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state) (available : Available state body)
    (annotated : Annotated valid body) (stored : MuStored valid state) :
    Checked valid (SourceRecursiveIntersectionMaybeMu.maybeMu key body state) (Annotated valid) := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq key body state state facts available]
  split
  · apply build valid _ _ state facts (InternedStoredSubstitution.leaves_available body state available)
    · simpa only [Allowed] using SourceEqualityAnnotationStoredSyntax.encode_allowed valid body annotated _ _
    · exact leaves_annotated valid body annotated
    · exact stored
  · exact checked_pure valid body state _ stored annotated

/-- Actual closed allowed construction initializes its local annotation and causal Mu store. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expression : Syntax Symbol Guard)
    (allowed : Allowed valid expression) :
    ∃ value state, InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      MuStored valid state ∧ Annotated valid value := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have checked := build valid expression [] empty empty_facts (by intro value member; cases member) allowed
    (by intro value member; cases member) (MuStored.empty valid)
  exact ⟨value, state, done, by simpa only [done, Outcome.state] using checked.stored, checked.result value state done⟩

end MicroCFTA.SourceCurrentHereditaryConstruction
