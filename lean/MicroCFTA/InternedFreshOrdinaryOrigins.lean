import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedStoredMuOrigins

/-!
# Actual stored origins under the repaired ordinary-name policy

Every completed recursive record retains the actual two probe callbacks,
the chosen ordinary argument, its missing reservation, and the fresh body call.
The invariant also holds at pending outcomes and after discarded child effects.
-/
namespace MicroCFTA.InternedFreshOrdinaryOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedStoredMuOrigins (filter_noNewMu)
open InternedConstructionProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)

/-- A complete payload keeps the exact original calls that produced its two probes and its fresh body. -/
def Origin [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) : Prop :=
  ∃ expression environment before afterDepth afterOrdinary afterBody,
    Facts before ∧ Values before environment ∧
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
/-- Every stored Mu after arbitrary source execution has its actual original probe and fresh-body calls. -/
theorem build_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Facts state) (inputs : Values state environment) (heap : Heap state) :
    Heap (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using heap
  | node edges =>
      rw [build]
      exact bind_heap _ _ (buildEdges_origins edges environment state normal inputs heap)
        (fun values after _ afterHeap => preserve after _ afterHeap (makeNode_noNewMu values after))
  | union members =>
      rw [build]
      exact bind_heap _ _ (buildMany_origins members environment state normal inputs heap)
        (fun values after _ afterHeap => preserve after _ afterHeap (makeUnion_noNewMu values after))
  | binder smart body =>
      have checked : ∀ name current, Facts current → Values current environment → Available current (.reference name) →
          Heap current → Heap (callback body environment name current).state := by
        intro name current currentFacts currentInputs argument currentHeap
        have all : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentInputs value member
        exact bind_heap _ _ (build_origins body _ current currentFacts all currentHeap)
          (fun value after _ afterHeap => preserve after _ afterHeap (filter_noNewMu name value after))
      have depthInputs : Values state (.reference .depth :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact depth_available state
        · exact inputs value member
      have depthFacts := (callback_verified body environment .depth state normal depthInputs).facts
      have depthVerified := callback_verified body environment .depth state normal depthInputs
      rw [build]
      change Heap ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary).state
      apply bind_heap _ _ (checked .depth state normal inputs (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap
      have depthFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using depthFacts
      have afterInputs : Values afterDepth environment := by
        intro value member
        simpa only [depthDone, Outcome.state] using depthVerified.available value (inputs value member)
      have ordinaryInputs : Values afterDepth (.reference (.uninterned (ordinaryLevel depth)) :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact ordinary_available afterDepth (ordinaryLevel depth)
        · exact afterInputs value member
      have ordinaryFacts := (callback_verified body environment (.uninterned (ordinaryLevel depth)) afterDepth depthFacts ordinaryInputs).facts
      have ordinaryVerified := callback_verified body environment (.uninterned (ordinaryLevel depth)) afterDepth depthFacts ordinaryInputs
      apply bind_heap _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthFacts afterInputs
        (ordinary_available afterDepth (ordinaryLevel depth)) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap
      have ordinaryFacts : Facts afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryFacts
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available value (afterInputs value member)
      cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
      | some entry =>
          cases present : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
            simpa only [request, found, present, Outcome.state] using ordinaryHeap
      | none =>
          let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
          let allocated := {afterOrdinary with nodes := entry.2}
          have reserved : Facts allocated := reserve_facts (muKey depth ordinary) afterOrdinary ordinaryFacts
          have growth : Grows afterOrdinary allocated :=
            ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
          have history := intern_issued_extends afterOrdinary.nodes (muKey depth ordinary) ordinaryFacts.coherent.valid.2
          have allocatedInputs : Values allocated environment :=
            fun value member => (finalInputs value member).grows afterOrdinary allocated growth history
          have freshAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
            (reserve_available (muKey depth ordinary) afterOrdinary ordinaryFacts.coherent ordinaryFacts.cached).2
          have allocatedHeap : Heap allocated := ordinaryHeap
          have actualHeap := checked (.interned entry.1.identity) allocated reserved allocatedInputs freshAvailable allocatedHeap
          simp only [request, found]
          change Heap ((callback body environment (.interned entry.1.identity) allocated).bind
            (fun value after => complete smart entry.1 value depth ordinary after)).state
          apply bind_heap _ _ actualHeap
          intro actual afterBody actualDone afterHeap
          exact complete_heap smart entry.1 actual depth ordinary afterBody afterHeap
            ⟨body, environment, state, afterDepth, afterOrdinary, afterBody, normal, inputs,
              depthDone, ordinaryDone, found, rfl, actualDone⟩
termination_by sizeOf expression

/-- Ordered source child construction preserves all complete recursive origins. -/
theorem buildMany_origins [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Facts state) (inputs : Values state environment) (heap : Heap state) :
    Heap (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      have checked := build_verified first environment state normal inputs
      have normalAfter := (build_verified first environment state normal inputs).facts
      rw [buildMany]
      apply bind_heap _ _ (build_origins first environment state normal inputs heap)
      intro value after returned afterHeap
      have afterFacts : Facts after := by simpa only [returned, Outcome.state] using normalAfter
      have afterInputs : Values after environment := by
        intro value member
        simpa only [returned, Outcome.state] using checked.available value (inputs value member)
      exact bind_heap _ _ (buildMany_origins rest environment after afterFacts afterInputs afterHeap)
        (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions

/-- Actual edge allocation and ordered siblings preserve every earlier recursive construction witness. -/
theorem buildEdges_origins [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Facts state) (inputs : Values state environment) (heap : Heap state) :
    Heap (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have checked := buildMany_verified children environment state normal inputs
          have normalAfter := (buildMany_verified children environment state normal inputs).facts
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_origins children environment state normal inputs heap)
          intro values after returned afterHeap
          have afterFacts : Facts after := by simpa only [returned, Outcome.state] using normalAfter
          have afterInputs : Values after environment := by
            intro value member
            simpa only [returned, Outcome.state] using checked.available value (inputs value member)
          have available := checked.result values after returned
          let result := run (makeEdge symbol constraint values) after
          have edgeFacts : Facts result.2 := (edge_verified symbol constraint values after afterFacts available).facts
          have edgeInputs : Values result.2 environment :=
            fun value member => available_after_run (makeEdge symbol constraint values) after afterFacts.coherent.valid (afterInputs value member)
          change Heap ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (buildEdges_origins rest environment result.2 edgeFacts edgeInputs afterHeap)
            (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions
end

/-- All complete recursive payloads in a first closed source run have actual construction origins, even if the run is pending. -/
theorem closed_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  build_origins expression [] empty empty_facts (by intro value member; cases member) empty_heap

end MicroCFTA.InternedFreshOrdinaryOrigins
