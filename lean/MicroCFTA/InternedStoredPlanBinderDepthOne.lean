import MicroCFTA.InternedStoredPlanBinderDepthFlat
import MicroCFTA.InternedFreshOrdinaryFirstOrderHeap
import MicroCFTA.InternedStoredLeafShape

/-!
# The positive depth-one case of repaired unfolding

A source plan with at most one binder on each path adds only Mu records
whose open body depth is zero. Earlier records can have arbitrary depth.
Closed captures can also have arbitrary cached depth.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepthOne
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedFacts InternedNestedRequestFacts InternedNestedProvenance
open InternedFreshProbeKeys InternedShallowHeap
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryFirstOrderHeap (callback_noNewMu)
open InternedStoredShallowCompletion InternedStoredPlanBinderDepth
open InternedBinderProtocol (Reference NodeKey)

/-- Every complete Mu is an exact earlier record or has an open body plan of depth zero. -/
def Heap (initial state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    initial.nodeRecords key = some (.mu entry body depth ordinary) ∨ valueDepth body = 0

variable {initial : State Symbol Guard}

/-- The initial cache retains each of its own exact records. -/
theorem refl_heap (state : State Symbol Guard) : Heap state state := by
  intro key entry body depth ordinary present
  exact Or.inl present

/-- Effects with no new Mu preserve the initial-record or zero-body alternatives. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap initial before)
    (old : NoNewMu before after) : Heap initial after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- Sequencing retains the property at the exact completed or pending cache. -/
theorem bind_heap (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (heap : Heap initial outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap initial after → Heap initial (next value after).state) :
    Heap initial (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- First-writer completion adds its actual zero-depth body or retains an earlier record. -/
theorem complete_zero (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap initial state) (zero : valueDepth body = 0) :
    Heap initial {state with nodeRecords := keepFirst state.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary)} := by
  intro key actual actualBody actualDepth actualOrdinary stored
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
      (.mu actual actualBody actualDepth actualOrdinary) stored with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact Or.inr zero

/-- A binder-free callback adds only zero-depth bodies and retains arbitrary earlier Mu records. -/
theorem binder_zero [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : BinderFree body) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (shallow : Heap initial state)
    (depths : ∀ value ∈ environment, valueDepth value = 0) :
    Heap initial (build (.binder smart body) environment state).state := by
  have invoke : ∀ name current, Facts current → Values current environment → Heap initial current →
      Available current (.reference name) →
      ∃ value after, callback body environment name current = .done value after ∧
        Facts after ∧ Values after environment ∧ Heap initial after ∧ valueDepth value = 0 := by
    intro name current currentFacts currentInputs currentHeap localAvailable
    have localInputs : Values current (.reference name :: environment) := by
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact localAvailable
      · exact currentInputs value member
    obtain ⟨value, after, done⟩ :=
      InternedFreshOrdinaryFirstOrderCompletion.callback_complete body free environment name current
    have checked := callback_verified body environment name current currentFacts localInputs
    have afterFacts : Facts after := by simpa only [done, Outcome.state] using checked.facts
    have afterInputs : Values after environment := fun item member => by
      simpa only [done, Outcome.state] using checked.available item (currentInputs item member)
    have afterHeap : Heap initial after := by
      have retained := preserve current _ currentHeap (callback_noNewMu body free environment name current)
      simpa only [done, Outcome.state] using retained
    have zero : valueDepth value = 0 := Nat.eq_zero_of_le_zero
      (InternedStoredPlanBinderDepthFlat.callback_bound body free environment name current currentFacts localInputs 0
        (fun item member => Nat.le_of_eq (depths item member)) value after done)
    exact ⟨value, after, done, afterFacts, afterInputs, afterHeap, zero⟩
  obtain ⟨depth, afterDepth, depthDone, depthFacts, depthInputs, depthShallow, _⟩ :=
    invoke .depth state facts inputs shallow (depth_available state)
  obtain ⟨ordinary, afterOrdinary, ordinaryDone, ordinaryFacts, ordinaryInputs, ordinaryShallow, _⟩ :=
    invoke (.uninterned (ordinaryLevel depth)) afterDepth depthFacts depthInputs depthShallow
      (ordinary_available afterDepth (ordinaryLevel depth))
  have expanded : build (.binder smart body) environment state =
      request smart depth ordinary (callback body environment) afterOrdinary := by
    rw [build]
    change (callback body environment .depth state).bind _ = _
    rw [depthDone]
    change (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _ = _
    rw [ordinaryDone]
    rfl
  rw [expanded]
  cases installed : afterOrdinary.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, stored, Outcome.state] using ordinaryShallow
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern afterOrdinary.nodes key
      let allocated := {afterOrdinary with nodes := entry.2}
      have allocatedFacts : Facts allocated := reserve_facts key afterOrdinary ordinaryFacts
      have reserved : Available allocated (.reference (.interned entry.1.identity)) :=
        (InternedConstructionProvenance.reserve_available key afterOrdinary ordinaryFacts.coherent ordinaryFacts.cached).2
      have growth : Grows afterOrdinary allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends afterOrdinary.nodes key ordinaryFacts.coherent.valid.2
      have allocatedInputs : Values allocated environment := fun value member =>
        (ordinaryInputs value member).grows afterOrdinary allocated growth history
      have allocatedHeap : Heap initial allocated := ordinaryShallow
      obtain ⟨actual, afterBody, actualDone, _, _, afterShallow, zero⟩ :=
        invoke (.interned entry.1.identity) allocated allocatedFacts allocatedInputs allocatedHeap reserved
      simp only [request, installed]
      change Heap initial ((callback body environment (.interned entry.1.identity) allocated).bind _).state
      rw [actualDone]
      simpa only [Outcome.bind, Outcome.state] using complete_zero entry.1 actual depth ordinary afterBody afterShallow zero


mutual
/-- A depth-one source plan adds only zero-depth Mu bodies from zero-depth lexical inputs. -/
theorem build_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (heap : Heap initial state)
    (depths : ∀ value ∈ environment, valueDepth value = 0) (limited : syntaxDepth expression ≤ 1) :
    Heap initial (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using heap
  | node edges =>
      rw [build]
      exact bind_heap _ _ (buildEdges_heap edges environment state facts inputs heap depths
        (by simpa only [syntaxDepth] using limited))
        (fun values after _ afterHeap => preserve after _ afterHeap (makeNode_noNewMu values after))
  | union members =>
      rw [build]
      exact bind_heap _ _ (buildMany_heap members environment state facts inputs heap depths
        (by simpa only [syntaxDepth] using limited))
        (fun values after _ afterHeap => preserve after _ afterHeap (makeUnion_noNewMu values after))
  | binder smart body =>
      have zero : syntaxDepth body = 0 := by rw [syntaxDepth] at limited; omega
      exact binder_zero smart body ((syntax_zero body).mp zero) environment state facts inputs heap depths
termination_by sizeOf expression

/-- Ordered child plans retain the exact initial-record or zero-body alternatives. -/
theorem buildMany_heap [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (heap : Heap initial state)
    (depths : ∀ value ∈ environment, valueDepth value = 0) (limited : syntaxManyDepth expressions ≤ 1) :
    Heap initial (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      have bounds : syntaxDepth first ≤ 1 ∧ syntaxManyDepth rest ≤ 1 := by
        simpa only [syntaxManyDepth, Nat.max_le] using limited
      have checked := InternedFreshOrdinaryFacts.build_verified first environment state facts inputs
      rw [buildMany]
      apply bind_heap _ _ (build_heap first environment state facts inputs heap depths bounds.1)
      intro value after returned afterHeap
      have afterFacts : Facts after := by simpa only [returned, Outcome.state] using checked.facts
      have afterInputs : Values after environment := by
        intro value member
        simpa only [returned, Outcome.state] using checked.available value (inputs value member)
      exact bind_heap _ _ (buildMany_heap rest environment after afterFacts afterInputs afterHeap depths bounds.2)
        (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions

/-- Edge effects and ordered siblings retain the source-plan depth-one guarantee. -/
theorem buildEdges_heap [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (heap : Heap initial state)
    (depths : ∀ value ∈ environment, valueDepth value = 0) (limited : syntaxEdgesDepth expressions ≤ 1) :
    Heap initial (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have bounds : syntaxManyDepth children ≤ 1 ∧ syntaxEdgesDepth rest ≤ 1 := by
            simpa only [syntaxEdgesDepth, Nat.max_le] using limited
          have checked := InternedFreshOrdinaryFacts.buildMany_verified children environment state facts inputs
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_heap children environment state facts inputs heap depths bounds.1)
          intro values after returned afterHeap
          have afterFacts : Facts after := by simpa only [returned, Outcome.state] using checked.facts
          have afterInputs : Values after environment := by
            intro value member
            simpa only [returned, Outcome.state] using checked.available value (inputs value member)
          have available := checked.result values after returned
          let result := run (makeEdge symbol constraint values) after
          have edgeFacts : Facts result.2 := (edge_verified symbol constraint values after afterFacts available).facts
          have edgeInputs : Values result.2 environment := fun value member =>
            available_after_run (makeEdge symbol constraint values) after afterFacts.coherent.valid (afterInputs value member)
          change Heap initial ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (buildEdges_heap rest environment result.2 edgeFacts edgeInputs afterHeap depths bounds.2)
            (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions
end

/-- The complete actual returned inventory has no new nonzero Mu body after a depth-one build. -/
theorem build_new_zero [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment)
    (depths : ∀ value ∈ environment, valueDepth value = 0) (limited : syntaxDepth expression ≤ 1) :
    Heap state (build expression environment state).state :=
  build_heap expression environment state facts inputs (refl_heap state) depths limited

/-- Actual depth-one stored substitution adds only zero-depth Mu bodies from zero-depth replacements. -/
theorem execute_new_zero [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value)
    (replacements : InternedStoredSubstitution.Replacements state environment)
    (depths : ∀ name replacement, environment name = some replacement → valueDepth replacement = 0)
    (limited : valueDepth value ≤ 1) :
    Heap state (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state := by
  have inputsDepth : ∀ selected ∈ (InternedStoredSubstitution.leaves value).map
      (InternedStoredSubstitution.input environment), valueDepth selected = 0 := by
    intro selected member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases InternedStoredLeafShape.leaves_shape value original present with closed | ⟨name, rfl⟩
    · rw [InternedStoredSubstitutionScope.input_closed original environment closed]
      exact closed_zero original closed
    · cases found : environment name with
      | none => simp [InternedStoredSubstitution.input, found, valueDepth, Value.free]
      | some replacement =>
          simpa only [InternedStoredSubstitution.input, found, Option.getD_some] using depths name replacement found
  exact build_new_zero _ _ state facts
    (InternedStoredSubstitution.inputs_available value environment state available replacements) inputsDepth
    (by rw [encode_depth]; exact limited)

/-- Actual unfolding of a closed depth-one body adds only zero-depth Mu bodies anywhere in the final cache. -/
theorem unfold_new_zero [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value)
    (closed : value.free = []) (limited : bodyDepth value ≤ 1) :
    Heap state (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact refl_heap state
  | mu entry body depth ordinary =>
      apply execute_new_zero body _ state facts (available.children body (by simp [children]))
      · intro name replacement found
        dsimp only at found
        split at found
        · cases found; exact available
        · contradiction
      · intro name replacement found
        split at found
        · cases found; exact closed_zero _ closed
        · contradiction
      · exact limited

/-- Every newly allocated Mu has strictly smaller body depth when the unfolded closed body has depth one. -/
theorem unfold_one_decreases [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value)
    (closed : value.free = []) (one : bodyDepth value = 1)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (new : state.nodeRecords key = none)
    (present : (InternedFreshOrdinaryStoredSubstitution.unfold value state).state.nodeRecords key =
      some (.mu entry body depth ordinary)) :
    bodyDepth (.mu entry body depth ordinary) < bodyDepth value := by
  have heap := unfold_new_zero value state facts available closed (by omega)
  rcases heap key entry body depth ordinary present with old | zero
  · rw [new] at old
    contradiction
  · change valueDepth body < bodyDepth value
    omega

end MicroCFTA.InternedStoredPlanBinderDepthOne
