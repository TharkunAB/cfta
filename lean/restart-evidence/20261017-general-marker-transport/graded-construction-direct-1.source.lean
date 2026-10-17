import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.SourceCurrentHereditaryConstruction

/-!
# Finite-cap syntax and actual mixed lexical construction

Each variable checks its actual lexical value at the requested depth.
Ordinary rows consume one depth. Unions retain that depth. Binder subplans
check depth zero for every fresh local reference. Unused constrained captures
remain permitted. The actual executor retains its conditional Mu store.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapConstruction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshProbeKeys InternedFreshOrdinaryConstruction
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryConstruction (MuStored Checked finish_annotated filter_checked)
open SourceCurrentConstrainedCap (Cap)

mutual
/-- Literal syntax uses each actual lexical value at its required finite constraint depth. -/
def Typed (valid : Guard → Prop) (depth : Nat) : Syntax Symbol Guard → List (Value Symbol Guard) → Prop
  | .empty, _ => True
  | .var index, environment => Cap valid depth (environment[index]?.getD .empty)
  | .node edges, environment => EdgesTyped valid depth edges environment
  | .union members, environment => ManyTyped valid depth members environment
  | .binder _ body, environment => ∀ name, Typed valid 0 body (.reference name :: environment)
termination_by expression _ => sizeOf expression

/-- Ordered subplans retain the same original lexical environment and depth. -/
def ManyTyped (valid : Guard → Prop) (depth : Nat) : List (Syntax Symbol Guard) → List (Value Symbol Guard) → Prop
  | [], _ => True
  | first :: rest, environment => Typed valid depth first environment ∧ ManyTyped valid depth rest environment
termination_by expressions _ => sizeOf expressions

/-- A literal row checks its guard only at zero and its children one depth below. -/
def EdgesTyped (valid : Guard → Prop) (depth : Nat) : List (EdgeSyntax Symbol Guard) → List (Value Symbol Guard) → Prop
  | [], _ => True
  | .mk _ guard children :: rest, environment =>
      (depth = 0 → valid guard) ∧ ManyTyped valid (depth - 1) children environment ∧ EdgesTyped valid depth rest environment
termination_by expressions _ => sizeOf expressions
end

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

private theorem checked_map {valid : Guard → Prop} {outcome : Outcome Symbol Guard A} {post last : A → Prop}
    (checked : Checked valid outcome post) (implies : ∀ value, post value → last value) : Checked valid outcome last :=
  ⟨checked.stored, fun value after done => implies value (checked.result value after done)⟩

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
/-- Actual graded construction derives its finite cap and retains Mu laws at its exact stopping state. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (typed : Typed valid depth expression environment) (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryConstruction.build expression environment state) (Cap valid depth) := by
  cases expression with
  | empty => simpa only [InternedFreshOrdinaryConstruction.build] using
      checked_pure valid (.empty : Value Symbol Guard) state (Cap valid depth) stored (Cap.plain depth Annotated.empty)
  | var index => simpa only [InternedFreshOrdinaryConstruction.build] using
      checked_pure valid (environment[index]?.getD .empty) state (Cap valid depth) stored typed
  | node edges =>
      have physical := InternedFreshOrdinaryFacts.buildEdges_verified edges environment state facts inputs
      rw [InternedFreshOrdinaryConstruction.build]
      apply checked_bind (buildEdges valid depth edges environment state facts inputs typed stored)
      intro values after done localRows kept
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using physical.facts
      have resident := physical.result values after done
      exact ⟨kept.makeNode values, fun result final returned => by
        obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
        exact SourceCurrentConstrainedCap.makeNode valid depth values after afterFacts.coherent afterFacts.linked resident localRows⟩
  | union members =>
      have physical := InternedFreshOrdinaryFacts.buildMany_verified members environment state facts inputs
      rw [InternedFreshOrdinaryConstruction.build]
      apply checked_bind (buildMany valid depth members environment state facts inputs typed stored)
      intro values after done localValues kept
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using physical.facts
      have available := physical.result values after done
      exact ⟨kept.makeUnion values, fun result final returned => by
        obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
        exact SourceCurrentConstrainedCap.makeUnion valid depth values after afterFacts available localValues⟩
  | binder smart body =>
      have hereditary : Checked valid (InternedFreshOrdinaryConstruction.build (.binder smart body) environment state) (Annotated valid) := by
        have calls (name : Reference) (current : State Symbol Guard) (currentFacts : Facts current)
            (currentInputs : Values current environment) (argument : Available current (.reference name))
            (kept : MuStored valid current) :
            Checked valid (InternedFreshOrdinaryFacts.callback body environment name current) (Annotated valid) := by
          have extended : Values current (.reference name :: environment) := by
            intro value member
            rcases List.mem_cons.mp member with rfl | member
            · exact argument
            · exact currentInputs value member
          have physical := InternedFreshOrdinaryFacts.build_verified body _ current currentFacts extended
          unfold InternedFreshOrdinaryFacts.callback
          have bodyChecked := build valid 0 body (.reference name :: environment) current currentFacts extended (typed name) kept
          apply checked_bind (checked_map bodyChecked (fun _ result => result.annotated rfl))
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
      exact checked_map hereditary (fun _ annotated => Cap.plain depth annotated)
termination_by sizeOf expression

/-- Actual child construction retains the finite cap at every literal returned position. -/
theorem buildMany [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat) (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (typed : ManyTyped valid depth expressions environment) (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryConstruction.buildMany expressions environment state)
      (fun values => ∀ value ∈ values, Cap valid depth value) := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildMany] using
      (checked_pure valid ([] : List (Value Symbol Guard)) state (fun values => ∀ value ∈ values, Cap valid depth value)
        stored (by intro value member; cases member))
  | cons first rest =>
      simp only [ManyTyped] at typed
      have physical := InternedFreshOrdinaryFacts.build_verified first environment state facts inputs
      rw [InternedFreshOrdinaryConstruction.buildMany]
      apply checked_bind (build valid depth first environment state facts inputs typed.1 stored)
      intro value middle done valueBounded middleStored
      have middleFacts : Facts middle := by simpa only [done, Outcome.state] using physical.facts
      have middleInputs : Values middle environment := fun child member => by
        simpa only [done, Outcome.state] using physical.available child (inputs child member)
      apply checked_bind (buildMany valid depth rest environment middle middleFacts middleInputs typed.2 middleStored)
      intro values after returned valuesBounded afterStored
      exact checked_pure valid (value :: values) after _ afterStored (by
        intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact valueBounded
        · exact valuesBounded child member)
termination_by sizeOf expressions

/-- Actual rows retain each finite child bound and each required zero-depth guard. -/
theorem buildEdges [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat) (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (typed : EdgesTyped valid depth expressions environment) (stored : MuStored valid state) :
    Checked valid (InternedFreshOrdinaryConstruction.buildEdges expressions environment state)
      (fun edges => ∀ edge ∈ edges, SourceCurrentConstrainedCap.Edge valid depth edge) := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildEdges] using
      (checked_pure valid ([] : List (EdgeValue Symbol Guard)) state (fun edges => ∀ edge ∈ edges, SourceCurrentConstrainedCap.Edge valid depth edge)
        stored (by intro edge member; cases member))
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [EdgesTyped] at typed
          have physical := InternedFreshOrdinaryFacts.buildMany_verified children environment state facts inputs
          rw [InternedFreshOrdinaryConstruction.buildEdges]
          apply checked_bind (buildMany valid (depth - 1) children environment state facts inputs typed.2.1 stored)
          intro values middle done valuesBounded middleStored
          have middleFacts : Facts middle := by simpa only [done, Outcome.state] using physical.facts
          have available := physical.result values middle done
          have edgePhysical := InternedNestedFacts.edge_verified symbol guard values middle middleFacts available
          have edgeChecked : Checked valid (work (InternedConstructorTemplates.makeEdge symbol guard values) middle)
              (SourceCurrentConstrainedCap.Edge valid depth) :=
            ⟨middleStored.makeEdge symbol guard values, fun edge after returned => by
              obtain ⟨rfl, rfl⟩ := Outcome.done.inj returned
              exact SourceCurrentConstrainedCap.makeEdge valid depth symbol guard values middle
                middleFacts.coherent middleFacts.cached available typed.1 valuesBounded⟩
          apply checked_bind edgeChecked
          intro edge cut built edgeBounded edgeStored
          have cutFacts : Facts cut := by simpa only [built, Outcome.state] using edgePhysical.facts
          have cutInputs : Values cut environment := fun value member => by
            have earlier : Available middle value := by
              simpa only [done, Outcome.state] using physical.available value (inputs value member)
            simpa only [built, Outcome.state] using edgePhysical.available value earlier
          apply checked_bind (buildEdges valid depth rest environment cut cutFacts cutInputs typed.2.2 edgeStored)
          intro edges after returned edgesBounded afterStored
          exact checked_pure valid (edge :: edges) after _ afterStored (by
            intro chosen member
            rcases List.mem_cons.mp member with rfl | member
            · exact edgeBounded
            · exact edgesBounded chosen member)
termination_by sizeOf expressions
end

end MicroCFTA.SourceCurrentConstrainedCapConstruction
