import MicroCFTA.InternedOpenDepthExecution
import MicroCFTA.InternedStoredLeafShape

/-!
# New Mu bodies have lower depth during actual repaired unfolding

Zero-depth lexical inputs remain fixed through source callbacks. Each new
Mu body comes from a strict subplan and satisfies its proved source bound.
All complete records in the returned cache are covered, including probes.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepthProgress
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (Values depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedStoredPlanBinderDepth
open InternedBinderProtocol (Reference NodeKey)

/-- Each complete Mu is an exact initial record or has body depth below the fixed source bound. -/
def Lower (initial : State Symbol Guard) (bound : Nat) (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    initial.nodeRecords key = some (.mu entry body depth ordinary) ∨ valueDepth body < bound

variable {initial : State Symbol Guard} {bound : Nat}

/-- Every initial record retains its own exact payload. -/
theorem lower_refl (state : State Symbol Guard) (bound : Nat) : Lower state bound state := by
  intro key entry body depth ordinary present
  exact Or.inl present

/-- Effects with no new Mu preserve the initial-record or lower-depth alternatives. -/
theorem preserve (before after : State Symbol Guard) (lower : Lower initial bound before)
    (old : NoNewMu before after) : Lower initial bound after := by
  intro key entry body depth ordinary present
  exact lower key entry body depth ordinary (old key entry body depth ordinary present)

/-- Sequencing retains the bound at the exact completed or pending cache. -/
theorem bind_lower (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result) (lower : Lower initial bound outcome.state)
    (later : ∀ value after, outcome = .done value after → Lower initial bound after → Lower initial bound (next value after).state) :
    Lower initial bound (outcome.bind next).state := by
  cases outcome with
  | pending => exact lower
  | done value after => exact later value after rfl lower

/-- First-writer completion installs its lower-depth candidate or retains an exact earlier record. -/
theorem complete_lower (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (lower : Lower initial bound state) (small : valueDepth body < bound) :
    Lower initial bound (complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact lower key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact Or.inr small

mutual
/-- Every actual source allocation respects the enclosing plan bound from zero-depth lexical inputs. -/
theorem build_lower [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedOpenDepthReadback.Heap state)
    (lower : Lower initial bound state) (zeros : ∀ value ∈ environment, valueDepth value = 0)
    (limited : syntaxDepth expression ≤ bound) : Lower initial bound (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using lower
  | node edges =>
      rw [build]
      exact bind_lower _ _ (buildEdges_lower edges environment state context cached heap lower zeros
        (by simpa only [syntaxDepth] using limited))
        (fun values after _ afterLower => preserve after _ afterLower (makeNode_noNewMu values after))
  | union members =>
      rw [build]
      exact bind_lower _ _ (buildMany_lower members environment state context cached heap lower zeros
        (by simpa only [syntaxDepth] using limited))
        (fun values after _ afterLower => preserve after _ afterLower (makeUnion_noNewMu values after))
  | binder smart body =>
      have bodySmall : syntaxDepth body < bound := by rw [syntaxDepth] at limited; omega
      have checked : ∀ argument current, Context current environment → Available current (.reference argument) →
          InternedFreshOrdinaryDepthHeap.Heap current → InternedOpenDepthReadback.Heap current →
          Lower initial bound current → Lower initial bound (callback body environment argument current).state := by
        intro argument current currentContext argumentAvailable currentCached currentHeap currentLower
        have inputsZero : ∀ value ∈ (.reference argument :: environment), valueDepth value = 0 := by
          intro value member
          rcases List.mem_cons.mp member with rfl | included
          · simp [valueDepth, Value.free]
          · exact zeros value included
        unfold callback
        exact bind_lower _ _ (build_lower body _ current (currentContext.local argument argumentAvailable)
          currentCached currentHeap currentLower inputsZero (Nat.le_of_lt bodySmall))
          (fun value after _ afterLower => preserve after _ afterLower (InternedStoredMuOrigins.filter_noNewMu argument value after))
      have depthOld := InternedRecordDepthExecution.callback_depth body environment .depth state context (depth_available state) cached
      have depthOpen := InternedOpenDepthExecution.callback_depth body environment .depth state context (depth_available state) cached heap
      rw [build]
      change Lower initial bound ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary).state
      apply bind_lower _ _ (checked .depth state context (depth_available state) cached heap lower)
      intro depth afterDepth depthDone depthLower
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthCached : InternedFreshOrdinaryDepthHeap.Heap afterDepth := by simpa only [depthDone, Outcome.state] using depthOld.heap
      have depthHeap : InternedOpenDepthReadback.Heap afterDepth := by simpa only [depthDone, Outcome.state] using depthOpen.heap
      have ordinaryOld := InternedRecordDepthExecution.callback_depth body environment (.uninterned (ordinaryLevel depth))
        afterDepth depthContext (ordinary_available afterDepth _) depthCached
      have ordinaryOpen := InternedOpenDepthExecution.callback_depth body environment (.uninterned (ordinaryLevel depth))
        afterDepth depthContext (ordinary_available afterDepth _) depthCached depthHeap
      apply bind_lower _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth _) depthCached depthHeap depthLower)
      intro ordinary afterOrdinary ordinaryDone ordinaryLower
      have finalContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have finalCached : InternedFreshOrdinaryDepthHeap.Heap afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryOld.heap
      have finalHeap : InternedOpenDepthReadback.Heap afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryOpen.heap
      cases installed : afterOrdinary.nodes.table (muKey depth ordinary) with
      | some entry =>
          cases present : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
            simpa only [request, installed, present, Outcome.state] using ordinaryLower
      | none =>
          let key := muKey depth ordinary
          let entry := Cache.intern afterOrdinary.nodes key
          let allocated := {afterOrdinary with nodes := entry.2}
          have reserved : Context allocated environment := finalContext.reserve key
          have argument : Available allocated (.reference (.interned entry.1.identity)) :=
            (InternedConstructionProvenance.reserve_available key afterOrdinary finalContext.normal.facts.coherent finalContext.normal.facts.cached).2
          have allocatedCached : InternedFreshOrdinaryDepthHeap.Heap allocated := finalCached
          have allocatedHeap : InternedOpenDepthReadback.Heap allocated := finalHeap
          have allocatedLower : Lower initial bound allocated := ordinaryLower
          simp only [request, installed]
          change Lower initial bound ((callback body environment (.interned entry.1.identity) allocated).bind
            (fun value after => complete smart entry.1 value depth ordinary after)).state
          apply bind_lower _ _ (checked (.interned entry.1.identity) allocated reserved argument
            allocatedCached allocatedHeap allocatedLower)
          intro actual afterBody actualDone afterLower
          have upper := InternedOpenDepthExecution.callback_bound body environment (.interned entry.1.identity)
            allocated reserved argument allocatedCached allocatedHeap 0 (fun value member => Nat.le_of_eq (zeros value member))
            actual afterBody actualDone
          exact complete_lower smart entry.1 actual depth ordinary afterBody afterLower (by omega)
termination_by sizeOf expression

/-- Ordered child plans retain the same enclosing allocation bound. -/
theorem buildMany_lower [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedOpenDepthReadback.Heap state)
    (lower : Lower initial bound state) (zeros : ∀ value ∈ environment, valueDepth value = 0)
    (limited : syntaxManyDepth expressions ≤ bound) : Lower initial bound (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using lower
  | cons first rest =>
      have bounds : syntaxDepth first ≤ bound ∧ syntaxManyDepth rest ≤ bound := by
        simpa only [syntaxManyDepth, Nat.max_le] using limited
      have old := InternedRecordDepthExecution.build_depth first environment state context cached
      have opened := InternedOpenDepthExecution.build_depth first environment state context cached heap
      rw [buildMany]
      apply bind_lower _ _ (build_lower first environment state context cached heap lower zeros bounds.1)
      intro value after returned afterLower
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.build first
      have afterCached : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [returned, Outcome.state] using old.heap
      have afterHeap : InternedOpenDepthReadback.Heap after := by simpa only [returned, Outcome.state] using opened.heap
      exact bind_lower _ _ (buildMany_lower rest environment after afterContext afterCached afterHeap afterLower zeros bounds.2)
        (fun _ _ _ laterLower => laterLower)
termination_by sizeOf expressions

/-- Actual edge effects and ordered siblings retain the enclosing allocation bound. -/
theorem buildEdges_lower [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedOpenDepthReadback.Heap state)
    (lower : Lower initial bound state) (zeros : ∀ value ∈ environment, valueDepth value = 0)
    (limited : syntaxEdgesDepth expressions ≤ bound) : Lower initial bound (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using lower
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have bounds : syntaxManyDepth children ≤ bound ∧ syntaxEdgesDepth rest ≤ bound := by
            simpa only [syntaxEdgesDepth, Nat.max_le] using limited
          have verified := buildMany_verified children environment state context.normal.facts context.inputs
          have old := InternedRecordDepthExecution.buildMany_depth children environment state context cached
          have opened := InternedOpenDepthExecution.buildMany_depth children environment state context cached heap
          rw [buildEdges]
          apply bind_lower _ _ (buildMany_lower children environment state context cached heap lower zeros bounds.1)
          intro values after returned afterLower
          have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many children
          have afterCached : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [returned, Outcome.state] using old.heap
          have afterHeap : InternedOpenDepthReadback.Heap after := by simpa only [returned, Outcome.state] using opened.heap
          have available := verified.result values after returned
          let actual := run (makeEdge symbol constraint values) after
          have edgeContext : Context actual.2 environment := afterContext.edge symbol constraint values available
          change Lower initial bound ((buildEdges rest environment actual.2).bind _).state
          exact bind_lower _ _ (buildEdges_lower rest environment actual.2 edgeContext afterCached afterHeap afterLower zeros bounds.2)
            (fun _ _ _ laterLower => laterLower)
termination_by sizeOf expressions
end

/-- Actual zero-depth lexical inputs derive lower depth for every newly completed Mu in the full final cache. -/
theorem build_new_lower [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedOpenDepthReadback.Heap state)
    (zeros : ∀ value ∈ environment, valueDepth value = 0) :
    Lower state (syntaxDepth expression) (build expression environment state).state :=
  build_lower expression environment state context cached heap (lower_refl state _) zeros (Nat.le_refl _)

/-- Actual stored lexical inputs retain the full source context of their available records. -/
theorem stored_context (value : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (available : Available state value)
    (replacements : InternedStoredSubstitution.Replacements state environment) :
    Context state ((InternedStoredSubstitution.leaves value).map (InternedStoredSubstitution.input environment)) :=
  ⟨context.normal, InternedStoredSubstitution.inputs_available value environment state available replacements,
    context.profiles, context.freeNames⟩

/-- Actual repaired stored substitution preserves the proved body/probe open-depth heap. -/
theorem execute_heap [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value)
    (replacements : InternedStoredSubstitution.Replacements state environment) :
    InternedOpenDepthReadback.Heap (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state :=
  (InternedOpenDepthExecution.build_depth _ _ state
    (stored_context value environment state context available replacements) cached heap).heap

/-- Actual repaired outer unfolding retains the body/probe open-depth heap for subsequent reads. -/
theorem unfold_heap [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) :
    InternedOpenDepthReadback.Heap (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      apply execute_heap body _ state context cached heap (available.children body (by simp [children]))
      intro name replacement found
      dsimp only at found
      split at found
      · cases found; exact available
      · contradiction

/-- Actual stored substitution derives lower body depth for every new Mu from zero-depth replacements. -/
theorem execute_new_lower [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value)
    (replacements : InternedStoredSubstitution.Replacements state environment)
    (zeros : ∀ name replacement, environment name = some replacement → valueDepth replacement = 0) :
    Lower state (valueDepth value) (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state := by
  have inputsZero : ∀ selected ∈ (InternedStoredSubstitution.leaves value).map
      (InternedStoredSubstitution.input environment), valueDepth selected = 0 := by
    intro selected member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases InternedStoredLeafShape.leaves_shape value original present with closed | ⟨name, rfl⟩
    · rw [InternedStoredSubstitutionScope.input_closed original environment closed]
      exact closed_zero original closed
    · cases found : environment name with
      | none => simp [InternedStoredSubstitution.input, found, valueDepth, Value.free]
      | some replacement =>
          simpa only [InternedStoredSubstitution.input, found, Option.getD_some] using zeros name replacement found
  have actual := build_new_lower (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves value) [] value)
    _ state (stored_context value environment state context available replacements) cached heap inputsZero
  simpa only [InternedFreshOrdinaryStoredSubstitution.execute, encode_depth] using actual

/-- Every Mu after actual closed unfolding is an exact earlier record or has strictly smaller body depth. -/
theorem unfold_new_lower [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = []) :
    Lower state (bodyDepth value) (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact lower_refl state _
  | mu entry body depth ordinary =>
      apply execute_new_lower body _ state context cached heap (available.children body (by simp [children]))
      · intro name replacement found
        dsimp only at found
        split at found
        · cases found; exact available
        · contradiction
      · intro name replacement found
        split at found
        · cases found; exact closed_zero _ closed
        · contradiction

/-- Every new Mu in the exact final cache of closed unfolding has strictly smaller body depth. -/
theorem unfold_decreases [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = [])
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (new : state.nodeRecords key = none)
    (present : (InternedFreshOrdinaryStoredSubstitution.unfold value state).state.nodeRecords key =
      some (.mu entry body depth ordinary)) : bodyDepth (.mu entry body depth ordinary) < bodyDepth value := by
  rcases unfold_new_lower value state context cached heap available closed key entry body depth ordinary present with old | small
  · rw [new] at old
    contradiction
  · exact small

/-- Actual empty-cache source construction derives every heap premise of strict closed-unfolding progress. -/
theorem constructed_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (available : Available (build expression [] empty).state value) (closed : value.free = [])
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (new : (build expression [] empty).state.nodeRecords key = none)
    (present : (InternedFreshOrdinaryStoredSubstitution.unfold value (build expression [] empty).state).state.nodeRecords key =
      some (.mu entry body depth ordinary)) : bodyDepth (.mu entry body depth ordinary) < bodyDepth value :=
  unfold_decreases value _ (empty_context.build expression)
    (InternedRecordDepthExecution.build_depth expression [] empty empty_context InternedFreshOrdinaryDepthHeap.empty_heap).heap
    (InternedOpenDepthExecution.closed_heap expression) available closed key entry body depth ordinary new present

end MicroCFTA.InternedStoredPlanBinderDepthProgress
