import MicroCFTA.SourceCurrentConstrainedCapSourceHistory

/-!
# Actual source Mu publication order

The execution history records all three callbacks before a Mu publication.
Each callback history is a strict subtree. A retained earlier winner keeps
its earlier publication. The history contains no output comparison law.
-/
namespace MicroCFTA.SourceCurrentNativeMuPublication
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedStoredMuOrigins (filter_noNewMu)
open InternedConstructionProvenance InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)

/-- A publication retains the literal source and its three completed callbacks. -/
structure Publication [DecidableEq (EdgeKey Symbol Guard)] where
  /-- The source requests raw or smart completion. -/
  smart : Bool
  /-- The source body is the same for all three calls. -/
  expression : Syntax Symbol Guard
  /-- The source captures remain fixed across the calls. -/
  environment : List (Value Symbol Guard)
  /-- The first callback starts at this actual state. -/
  before : State Symbol Guard
  /-- The Depth callback returns this state. -/
  afterDepth : State Symbol Guard
  /-- The ordinary callback returns this state before reservation. -/
  cut : State Symbol Guard
  /-- The reserved body callback returns this state before publication. -/
  afterBody : State Symbol Guard
  /-- The first callback returns the actual Depth value. -/
  depth : Value Symbol Guard
  /-- The second callback returns the actual ordinary value. -/
  ordinary : Value Symbol Guard
  /-- The reserved callback returns the actual body value. -/
  body : Value Symbol Guard
  /-- The initial callback point has its causal source context. -/
  context : Context before environment
  /-- The first callback uses the Depth reference. -/
  depthDone : callback expression environment .depth before = .done depth afterDepth
  /-- The second callback uses the repaired level selected from Depth. -/
  ordinaryDone : callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth =
    .done ordinary cut
  /-- The request misses before it reserves its entry. -/
  missing : cut.nodes.table (muKey depth ordinary) = none
  /-- The third callback uses the exact reserved entry and state. -/
  bodyDone : callback expression environment
    (.interned (Cache.intern cut.nodes (muKey depth ordinary)).1.identity)
    {cut with nodes := (Cache.intern cut.nodes (muKey depth ordinary)).2} = .done body afterBody

/-- The actual missing key identifies this publication. -/
def Publication.key [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) : NodeKey :=
  muKey event.depth event.ordinary

/-- The actual reservation selects the entry before the body callback. -/
def Publication.entry [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) : Interned NodeKey :=
  (Cache.intern event.cut.nodes event.key).1

/-- Reservation changes the cache before the third callback. -/
def Publication.allocated [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) : State Symbol Guard :=
  {event.cut with nodes := (Cache.intern event.cut.nodes event.key).2}

/-- The candidate contains the actual three callback outputs. -/
def Publication.candidate [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) : Value Symbol Guard :=
  .mu event.entry event.body event.depth event.ordinary

/-- Completion retains the exact first-writer payload update. -/
def Publication.after [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) : State Symbol Guard :=
  (complete event.smart event.entry event.body event.depth event.ordinary event.afterBody).state

/-- The actual return cleans up the selected winner, which can precede this candidate. -/
def Publication.result [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) : Value Symbol Guard :=
  finish event.smart ((keepFirst event.afterBody.nodeRecords event.key event.candidate event.key).getD event.candidate)

/-- Every publication contains the earlier joint origin contract. -/
theorem Publication.origin [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    SourceCurrentConstrainedCapSourceHistory.Origin event.entry event.body event.depth event.ordinary :=
  ⟨event.expression, event.environment, event.before, event.afterDepth, event.cut, event.afterBody,
    event.context, event.depthDone, event.ordinaryDone, event.missing, rfl, event.bodyDone⟩

/-- A finite actual publication history keeps all callback histories as subtrees. -/
inductive History [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → State Symbol Guard → Type where
  /-- No source instruction changes this state. -/
  | refl (state) : History state state
  /-- This actual effect adds no completed Mu payload. -/
  | retain (before after) (old : NoNewMu before after) : History before after
  /-- The actual first segment completes before the next segment starts. -/
  | trans {before middle after} (first : History before middle) (next : History middle after) : History before after
  /-- A completed miss publishes after all three actual callback histories. -/
  | publication (event : Publication (Symbol := Symbol) (Guard := Guard))
      (depth : History event.before event.afterDepth)
      (ordinary : History event.afterDepth event.cut)
      (body : History event.allocated event.afterBody) : History event.before event.after

private def bind_history [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard)
    (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : History before outcome.state)
    (later : ∀ value after, outcome = .done value after → History after (next value after).state) :
    History before (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value after => exact .trans first (later value after rfl)

private def binder_history [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment)
    (checked : ∀ name current, Context current environment → Available current (.reference name) →
      History current (callback expression environment name current).state) :
    History state ((callback expression environment .depth state).bind fun depth afterDepth =>
      (callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary cut =>
        request smart depth ordinary (callback expression environment) cut).state := by
  have depthHistory := checked .depth state context (depth_available state)
  cases depthDone : callback expression environment .depth state with
  | pending key after => simpa only [depthDone, Outcome.bind, Outcome.state] using depthHistory
  | done depth afterDepth =>
      have depthHistory' : History state afterDepth := by simpa only [depthDone, Outcome.state] using depthHistory
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback expression .depth (depth_available state)
      have ordinaryHistory := checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth (ordinaryLevel depth))
      simp only [Outcome.bind]
      cases ordinaryDone : callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth with
      | pending key after =>
          exact .trans depthHistory' (by simpa only [ordinaryDone, Outcome.state] using ordinaryHistory)
      | done ordinary cut =>
          have ordinaryHistory' : History afterDepth cut := by simpa only [ordinaryDone, Outcome.state] using ordinaryHistory
          have cutContext : Context cut environment := by
            simpa only [ordinaryDone, Outcome.state] using depthContext.callback expression
              (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth (ordinaryLevel depth))
          cases missing : cut.nodes.table (muKey depth ordinary) with
          | some entry =>
              cases found : cut.nodeRecords (muKey depth ordinary) <;>
                simpa only [request, missing, found, Outcome.state] using .trans depthHistory' ordinaryHistory'
          | none =>
              let entry := Cache.intern cut.nodes (muKey depth ordinary)
              let allocated := {cut with nodes := entry.2}
              have reserveHistory : History cut allocated := .retain cut allocated (fun _ _ _ _ _ present => present)
              have reserved : Context allocated environment := cutContext.reserve (muKey depth ordinary)
              have argument : Available allocated (.reference (.interned entry.1.identity)) :=
                (reserve_available (muKey depth ordinary) cut cutContext.base.normal.facts.coherent
                  cutContext.base.normal.facts.cached).2
              have bodyHistory := checked (.interned entry.1.identity) allocated reserved argument
              simp only [request, missing]
              change History state ((callback expression environment (.interned entry.1.identity) allocated).bind
                (fun value after => complete smart entry.1 value depth ordinary after)).state
              cases bodyDone : callback expression environment (.interned entry.1.identity) allocated with
              | pending key after =>
                  exact .trans (.trans depthHistory' ordinaryHistory') (.trans reserveHistory
                    (by simpa only [bodyDone, Outcome.bind, Outcome.state] using bodyHistory))
              | done body afterBody =>
                  let event : Publication (Symbol := Symbol) (Guard := Guard) :=
                    ⟨smart, expression, environment, state, afterDepth, cut, afterBody, depth, ordinary, body,
                      context, depthDone, ordinaryDone, missing, bodyDone⟩
                  exact History.publication event depthHistory' ordinaryHistory'
                    (by
                      change History allocated afterBody
                      simpa only [bodyDone, Outcome.state] using bodyHistory)

mutual
/-- Full repaired source execution produces its actual publication history at every stopping state. -/
theorem build_history [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) :
    Nonempty (History state (build expression environment state).state) := by
  apply Nonempty.intro
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using History.refl state
  | node edges =>
      rw [build]
      exact bind_history state _ _ (Classical.choice (buildEdges_history edges environment state context))
        (fun values after _ => .retain after _ (makeNode_noNewMu values after))
  | union members =>
      rw [build]
      exact bind_history state _ _ (Classical.choice (buildMany_history members environment state context))
        (fun values after _ => .retain after _ (makeUnion_noNewMu values after))
  | binder smart body =>
      rw [build]
      apply binder_history smart body environment state context
      intro name current currentContext argument
      exact bind_history current _ _ (Classical.choice (build_history body _ current (currentContext.local name argument)))
        (fun value after _ => .retain after _ (filter_noNewMu name value after))
termination_by sizeOf expression

/-- Ordered child construction produces the histories of the children that actually execute. -/
theorem buildMany_history [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) :
    Nonempty (History state (buildMany expressions environment state).state) := by
  apply Nonempty.intro
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using History.refl state
  | cons first rest =>
      rw [buildMany]
      apply bind_history state _ _ (Classical.choice (build_history first environment state context))
      intro value after returned
      have afterContext : Context after environment := by
        simpa only [returned, Outcome.state] using context.build first
      exact bind_history after _ _ (Classical.choice (buildMany_history rest environment after afterContext))
        (fun _ final _ => .refl final)
termination_by sizeOf expressions

/-- Ordered rows retain callback histories even when normalization discards a row. -/
theorem buildEdges_history [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) :
    Nonempty (History state (buildEdges expressions environment state).state) := by
  apply Nonempty.intro
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using History.refl state
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [buildEdges]
          apply bind_history state _ _ (Classical.choice (buildMany_history children environment state context))
          intro values after returned
          have afterContext : Context after environment := by
            simpa only [returned, Outcome.state] using context.many children
          have available := (buildMany_verified children environment state context.base.normal.facts
            context.base.inputs).result values after returned
          let result := run (makeEdge symbol guard values) after
          have edgeContext : Context result.2 environment := afterContext.edge symbol guard values available
          change History after ((buildEdges rest environment result.2).bind _).state
          exact .trans (.retain after result.2 (fun _ _ _ _ _ present => present))
            (bind_history result.2 _ _ (Classical.choice (buildEdges_history rest environment result.2 edgeContext))
              (fun _ final _ => .refl final))
termination_by sizeOf expressions
end

/-- A closed source starts this history at the actual empty tables. -/
noncomputable def closed_history [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    History empty (build expression [] empty).state :=
  Classical.choice (build_history expression [] empty SourceCurrentConstrainedCapSourceHistory.empty_context)

/-- The publication's three calls reconstruct the literal enclosing binder return. -/
theorem Publication.build_done [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    build (.binder event.smart event.expression) event.environment event.before =
      .done event.result event.after := by
  rw [build]
  change ((callback event.expression event.environment .depth event.before).bind fun depth afterDepth =>
    (callback event.expression event.environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary cut =>
      request event.smart depth ordinary (callback event.expression event.environment) cut) = _
  rw [event.depthDone]
  simp only [Outcome.bind]
  rw [event.ordinaryDone]
  simp only [Outcome.bind, request, event.missing]
  change ((callback event.expression event.environment (.interned event.entry.identity) event.allocated).bind _) = _
  have bodyDone : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  rw [bodyDone]
  rfl

/-- A writer retains its initial prefix and all callback histories before publication. -/
def Written [DecidableEq (EdgeKey Symbol Guard)] (start : State Symbol Guard)
    (key : NodeKey) (value : Value Symbol Guard) : Prop :=
  ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
    key = event.key ∧ value = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
    Nonempty (History start event.before) ∧
    Nonempty (History event.before event.afterDepth) ∧
    Nonempty (History event.afterDepth event.cut) ∧
    Nonempty (History event.allocated event.afterBody)

/-- An earlier execution prefix changes neither a writer nor its callback histories. -/
theorem Written.prepend [DecidableEq (EdgeKey Symbol Guard)] {before middle : State Symbol Guard}
    {key : NodeKey} {value : Value Symbol Guard} (earlier : History before middle)
    (written : Written middle key value) : Written before key value := by
  obtain ⟨event, sameKey, sameValue, firstWrite, ⟨first⟩, depth, ordinary, body⟩ := written
  exact ⟨event, sameKey, sameValue, firstWrite, ⟨.trans earlier first⟩, depth, ordinary, body⟩

/-- Every final Mu record came from the initial table or an actual earlier publication. -/
theorem History.writers [DecidableEq (EdgeKey Symbol Guard)] (history : History before after)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Written before key (.mu entry body depth ordinary) := by
  induction history with
  | refl => exact Or.inl present
  | retain before after old => exact Or.inl (old key entry body depth ordinary present)
  | trans first next firstIH nextIH =>
      rcases nextIH present with old | written
      · exact firstIH old
      · exact Or.inr (Written.prepend first written)
  | publication event depthHistory ordinaryHistory bodyHistory depthIH ordinaryIH bodyIH =>
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨sameKey, sameValue⟩
      · rcases bodyIH old with oldAllocated | written
        · rcases ordinaryIH oldAllocated with oldDepth | written
          · exact depthIH oldDepth
          · exact Or.inr (Written.prepend depthHistory written)
        · exact Or.inr (Written.prepend (.trans (.trans depthHistory ordinaryHistory)
            (.retain event.cut event.allocated (fun _ _ _ _ _ found => found))) written)
      · cases firstWrite : event.afterBody.nodeRecords event.key with
        | none => exact Or.inr ⟨event, sameKey, sameValue, firstWrite, ⟨.refl event.before⟩,
            ⟨depthHistory⟩, ⟨ordinaryHistory⟩, ⟨bodyHistory⟩⟩
        | some previous =>
            have old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary) := by
              change keepFirst event.afterBody.nodeRecords event.key event.candidate key =
                some (.mu entry body depth ordinary) at present
              simpa only [keepFirst, firstWrite] using present
            rcases bodyIH old with oldAllocated | written
            · rcases ordinaryIH oldAllocated with oldDepth | written
              · exact depthIH oldDepth
              · exact Or.inr (Written.prepend depthHistory written)
            · exact Or.inr (Written.prepend (.trans (.trans depthHistory ordinaryHistory)
                (.retain event.cut event.allocated (fun _ _ _ _ _ found => found))) written)

/-- Empty initial tables turn every completed Mu read into a causal writer witness. -/
theorem History.from_empty [DecidableEq (EdgeKey Symbol Guard)] (history : History empty after)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    Written empty key (.mu entry body depth ordinary) := by
  rcases history.writers key entry body depth ordinary present with impossible | written
  · cases impossible
  · exact written

/-- A closed actual source build produces a writer witness for every completed Mu. -/
theorem closed_writer [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    Written empty key (.mu entry body depth ordinary) :=
  (closed_history expression).from_empty key entry body depth ordinary present

end MicroCFTA.SourceCurrentNativeMuPublication
