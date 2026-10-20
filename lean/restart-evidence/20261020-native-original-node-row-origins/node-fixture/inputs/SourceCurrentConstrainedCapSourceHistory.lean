import MicroCFTA.InternedFreshOrdinarySemanticOrigins
import MicroCFTA.InternedRecordDepthExecution

/-!
# Joint semantic evidence at actual source construction histories

Each completed Mu record retains its actual pre-probe context and depth
heap. Full source execution preserves this history at every stopping state.
The invariant retains an earlier first-writer history when a later candidate
is discarded. It does not establish a guard-profile observation or cap law.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSourceHistory
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedStoredMuOrigins (filter_noNewMu)
open InternedConstructionProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)

/-- The actual source point retains all semantic heaps and its available captures. -/
structure Context (state : State Symbol Guard) (environment : List (Value Symbol Guard)) : Prop where
  /-- The earlier semantic context retains normalization, captures, profiles, and free names. -/
  base : InternedFreshOrdinaryContext.Context state environment
  /-- The same historical heap retains decoded depth and deep-name observations. -/
  depth : InternedFreshOrdinaryDepthHeap.Heap state

/-- Empty tables establish the joint context without completed-record assumptions. -/
theorem empty_context : Context (empty (Symbol := Symbol) (Guard := Guard)) [] :=
  ⟨InternedFreshOrdinaryContext.empty_context, InternedFreshOrdinaryDepthHeap.empty_heap⟩

/-- Actual expression execution retains the joint context at its stopping state. -/
theorem Context.build [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expression : Syntax Symbol Guard) : Context (build expression environment state).state environment :=
  ⟨context.base.build expression,
    (InternedRecordDepthExecution.build_depth expression environment state context.base context.depth).heap⟩

/-- Actual ordered capture execution retains the joint context at its stopping state. -/
theorem Context.many [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expressions : List (Syntax Symbol Guard)) : Context (buildMany expressions environment state).state environment :=
  ⟨context.base.many expressions,
    (InternedRecordDepthExecution.buildMany_depth expressions environment state context.base context.depth).heap⟩

/-- Actual ordered edge execution retains the joint context at its stopping state. -/
theorem Context.edges [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expressions : List (EdgeSyntax Symbol Guard)) : Context (buildEdges expressions environment state).state environment :=
  ⟨context.base.edges expressions,
    (InternedRecordDepthExecution.buildEdges_depth expressions environment state context.base context.depth).heap⟩

/-- An available local reference changes neither semantic heap. -/
theorem Context.local (context : Context state environment) (name : Reference)
    (available : Available state (.reference name)) : Context state (.reference name :: environment) :=
  ⟨context.base.local name available, context.depth⟩

/-- The actual normalized callback retains all historical observation heaps. -/
theorem Context.callback [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expression : Syntax Symbol Guard) (name : Reference) (available : Available state (.reference name)) :
    Context (callback expression environment name state).state environment :=
  ⟨context.base.callback expression name available,
    (InternedRecordDepthExecution.callback_depth expression environment name state context.base available context.depth).heap⟩

/-- Ordinary edge allocation retains all historical observation heaps. -/
theorem Context.edge [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (inputs : Values state values) :
    Context (run (makeEdge symbol guard values) state).2 environment :=
  ⟨context.base.edge symbol guard values inputs, context.depth⟩

/-- A fresh reservation retains all historical observation heaps. -/
theorem Context.reserve (context : Context state environment) (key : NodeKey) :
    Context {state with nodes := (Cache.intern state.nodes key).2} environment :=
  ⟨context.base.reserve key, context.depth⟩

/-- A complete payload retains the joint context and exact calls before its original probes and body. -/
def Origin [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) : Prop :=
  ∃ expression environment before afterDepth afterOrdinary afterBody,
    Context before environment ∧
    callback expression environment .depth before = .done depth afterDepth ∧
    callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary afterOrdinary ∧
    afterOrdinary.nodes.table (muKey depth ordinary) = none ∧
    entry = (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1 ∧
    callback expression environment (.interned entry.identity)
      {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2} = .done body afterBody

/-- Each complete stored Mu payload retains its original joint source history. -/
def Heap [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Origin entry body depth ordinary

/-- Joint historical evidence retains the earlier semantic origin contract. -/
theorem Origin.base [DecidableEq (EdgeKey Symbol Guard)] {entry : Interned NodeKey}
    {body depth ordinary : Value Symbol Guard} (origin : Origin entry body depth ordinary) :
    InternedFreshOrdinarySemanticOrigins.Origin entry body depth ordinary := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody,
    context, depthDone, ordinaryDone, missing, actualEntry, bodyDone⟩ := origin
  exact ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody,
    context.base, depthDone, ordinaryDone, missing, actualEntry, bodyDone⟩

/-- The stronger source history retains every earlier semantic origin. -/
theorem Heap.base [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard} (heap : Heap state) :
    InternedFreshOrdinarySemanticOrigins.Heap state := by
  intro key entry body depth ordinary present
  exact (heap key entry body depth ordinary present).base

/-- Empty tables have no origin obligations. -/
theorem empty_heap [DecidableEq (EdgeKey Symbol Guard)] : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Effects that introduce no Mu preserve the exact earlier source origins. -/
theorem preserve [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (heap : Heap before) (old : NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- Source sequencing threads historical payload origins through the actual stopping state. -/
theorem bind_heap [DecidableEq (EdgeKey Symbol Guard)] (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (heap : Heap outcome.state) (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- A completed constructor adds its own exact origin or retains an immutable earlier payload. -/
theorem complete_heap [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (heap : Heap state) (origin : Origin entry body depth ordinary) : Heap (complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact origin

mutual
/-- Every actual expression retains the joint historical context for every completed Mu. -/
theorem build_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Heap (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using heap
  | node edges =>
      rw [build]
      exact bind_heap _ _ (buildEdges_origins edges environment state context heap)
        (fun values after _ afterHeap => preserve after _ afterHeap (makeNode_noNewMu values after))
  | union members =>
      rw [build]
      exact bind_heap _ _ (buildMany_origins members environment state context heap)
        (fun values after _ afterHeap => preserve after _ afterHeap (makeUnion_noNewMu values after))
  | binder smart body =>
      have checked : ∀ name current, Context current environment → Available current (.reference name) →
          Heap current → Heap (callback body environment name current).state := by
        intro name current currentContext argument currentHeap
        exact bind_heap _ _ (build_origins body _ current (currentContext.local name argument) currentHeap)
          (fun value after _ afterHeap => preserve after _ afterHeap (filter_noNewMu name value after))
      rw [build]
      change Heap ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary).state
      apply bind_heap _ _ (checked .depth state context (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      apply bind_heap _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth (ordinaryLevel depth)) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap
      have ordinaryContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using
          depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth (ordinaryLevel depth))
      cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
      | some entry =>
          cases present : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
            simpa only [request, found, present, Outcome.state] using ordinaryHeap
      | none =>
          let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
          let allocated := {afterOrdinary with nodes := entry.2}
          have reserved : Context allocated environment := ordinaryContext.reserve (muKey depth ordinary)
          have freshAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
            (reserve_available (muKey depth ordinary) afterOrdinary ordinaryContext.base.normal.facts.coherent ordinaryContext.base.normal.facts.cached).2
          have actualHeap := checked (.interned entry.1.identity) allocated reserved freshAvailable ordinaryHeap
          simp only [request, found]
          change Heap ((callback body environment (.interned entry.1.identity) allocated).bind
            (fun value after => complete smart entry.1 value depth ordinary after)).state
          apply bind_heap _ _ actualHeap
          intro actual afterBody actualDone afterHeap
          exact complete_heap smart entry.1 actual depth ordinary afterBody afterHeap
            ⟨body, environment, state, afterDepth, afterOrdinary, afterBody, context,
              depthDone, ordinaryDone, found, rfl, actualDone⟩
termination_by sizeOf expression

/-- Ordered child effects retain all historical semantic contexts. -/
theorem buildMany_origins [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Heap (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      rw [buildMany]
      apply bind_heap _ _ (build_origins first environment state context heap)
      intro value after returned afterHeap
      have afterContext : Context after environment := by
        simpa only [returned, Outcome.state] using context.build first
      exact bind_heap _ _ (buildMany_origins rest environment after afterContext afterHeap)
        (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions

/-- Discarded edge computations retain the same actual origin evidence as retained computations. -/
theorem buildEdges_origins [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Heap (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_origins children environment state context heap)
          intro values after returned afterHeap
          have afterContext : Context after environment := by
            simpa only [returned, Outcome.state] using context.many children
          have available := (buildMany_verified children environment state context.base.normal.facts context.base.inputs).result values after returned
          let result := run (makeEdge symbol constraint values) after
          have edgeContext : Context result.2 environment := afterContext.edge symbol constraint values available
          change Heap ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (buildEdges_origins rest environment result.2 edgeContext afterHeap)
            (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions
end

/-- A closed source run derives joint historical evidence at every stopping state. -/
theorem closed_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  build_origins expression [] empty empty_context empty_heap

end MicroCFTA.SourceCurrentConstrainedCapSourceHistory
