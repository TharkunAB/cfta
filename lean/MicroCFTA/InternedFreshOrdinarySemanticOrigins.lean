import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedStoredMuOrigins

/-!
# Semantic source contexts at repaired recursive construction origins

Every completed recursive record retains the actual two probe callbacks,
the chosen ordinary argument, its missing reservation, and the fresh body call.
The invariant also holds at pending outcomes and after discarded child effects.
-/
namespace MicroCFTA.InternedFreshOrdinarySemanticOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedStoredMuOrigins (filter_noNewMu)
open InternedConstructionProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedBinderProtocol (Reference NodeKey)

/-- A complete payload keeps the exact original calls that produced its two probes and its fresh body. -/
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

/-- Every complete stored Mu payload has an original source construction. -/
def Heap [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Origin entry body depth ordinary

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
/-- Complete records retain the actual semantic context before their original probes. -/
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
            (reserve_available (muKey depth ordinary) afterOrdinary ordinaryContext.normal.facts.coherent ordinaryContext.normal.facts.cached).2
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
          have available := (buildMany_verified children environment state context.normal.facts context.inputs).result values after returned
          let result := run (makeEdge symbol constraint values) after
          have edgeContext : Context result.2 environment := afterContext.edge symbol constraint values available
          change Heap ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (buildEdges_origins rest environment result.2 edgeContext afterHeap)
            (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions
end

/-- Every completed recursive payload retains its proved semantic source context after a closed run. -/
theorem closed_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  build_origins expression [] empty empty_context empty_heap

end MicroCFTA.InternedFreshOrdinarySemanticOrigins
