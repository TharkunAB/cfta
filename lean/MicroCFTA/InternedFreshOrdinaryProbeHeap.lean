import MicroCFTA.InternedFreshOrdinaryProbeFilter

/-!
# Both filtered probes through actual repaired source effects

Each complete Mu retains the root filtering of its Depth and ordinary
probes. Source execution preserves this physical invariant at completed and
pending outcomes. It needs no original-call history for earlier records.
-/
namespace MicroCFTA.InternedFreshOrdinaryProbeHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedStoredMuOrigins (filter_noNewMu)
open InternedConstructionProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshOrdinaryProbeFilter (Clean callback_clean)

/-- Every completed Mu retains both actual filtered probe records. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Clean depth ordinary

/-- Empty tables contain no Mu probe obligations. -/
theorem empty_heap [DecidableEq (EdgeKey Symbol Guard)] : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Effects that introduce no Mu retain both filtered probes in earlier records. -/
theorem preserve [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (heap : Heap before) (old : NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- Source sequencing retains filtered probes at its actual stopping state. -/
theorem bind_heap [DecidableEq (EdgeKey Symbol Guard)] (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (heap : Heap outcome.state) (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- Completion installs the two actual filtered probes or retains the earlier complete payload. -/
theorem complete_heap [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (heap : Heap state) (clean : Clean depth ordinary) : Heap (complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact clean

mutual
/-- Actual source execution derives filtering for new probes and retains all earlier records. -/
theorem build_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Heap (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using heap
  | node edges =>
      rw [build]
      exact bind_heap _ _ (buildEdges_heap edges environment state context heap)
        (fun values after _ afterHeap => preserve after _ afterHeap (makeNode_noNewMu values after))
  | union members =>
      rw [build]
      exact bind_heap _ _ (buildMany_heap members environment state context heap)
        (fun values after _ afterHeap => preserve after _ afterHeap (makeUnion_noNewMu values after))
  | binder smart body =>
      have checked : ∀ name current, Context current environment → Available current (.reference name) →
          Heap current → Heap (callback body environment name current).state := by
        intro name current currentContext argument currentHeap
        exact bind_heap _ _ (build_heap body _ current (currentContext.local name argument) currentHeap)
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
          intro actual afterBody _actualDone afterHeap
          exact complete_heap smart entry.1 actual depth ordinary afterBody afterHeap
            ⟨callback_clean body environment .depth state afterDepth context (depth_available state) depth depthDone,
              callback_clean body environment (.uninterned (ordinaryLevel depth)) afterDepth afterOrdinary depthContext
                (ordinary_available afterDepth (ordinaryLevel depth)) ordinary ordinaryDone⟩
termination_by sizeOf expression

/-- Ordered child effects preserve both probes through actual returned caches. -/
theorem buildMany_heap [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Heap (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      rw [buildMany]
      apply bind_heap _ _ (build_heap first environment state context heap)
      intro value after returned afterHeap
      have afterContext : Context after environment := by
        simpa only [returned, Outcome.state] using context.build first
      exact bind_heap _ _ (buildMany_heap rest environment after afterContext afterHeap)
        (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions

/-- Discarded edge computations retain the same probe invariant as retained computations. -/
theorem buildEdges_heap [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Heap (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_heap children environment state context heap)
          intro values after returned afterHeap
          have afterContext : Context after environment := by
            simpa only [returned, Outcome.state] using context.many children
          have available := (buildMany_verified children environment state context.normal.facts context.inputs).result values after returned
          let result := run (makeEdge symbol constraint values) after
          have edgeContext : Context result.2 environment := afterContext.edge symbol constraint values available
          change Heap ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (buildEdges_heap rest environment result.2 edgeContext afterHeap)
            (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions
end

/-- Original closed source execution derives the invariant for every complete Mu record. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  build_heap expression [] empty empty_context empty_heap

/-- Residency exposes both filtered probes without an original-call history premise. -/
theorem resident (state : State Symbol Guard) (heap : Heap state) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (available : Available state (.mu entry body depth ordinary)) :
    Clean depth ordinary := heap entry.key entry body depth ordinary (available.resident entry rfl)

/-- Ordinary source node construction adds no recursive payload. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (heap : Heap state) : Heap (run (makeNode edges) state).2 :=
  preserve state _ heap (makeNode_noNewMu edges state)

/-- Actual source union normalization adds no recursive payload. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap state) : Heap (run (makeUnion values) state).2 :=
  preserve state _ heap (makeUnion_noNewMu values state)

/-- Actual bare-self filtering adds no recursive payload. -/
theorem filter [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) : Heap (run (withoutSelfReference name value) state).2 :=
  preserve state _ heap (filter_noNewMu name value state)

/-- Actual edge interning retains every complete node payload. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap state) : Heap (run (makeEdge symbol guard values) state).2 := heap

end MicroCFTA.InternedFreshOrdinaryProbeHeap
