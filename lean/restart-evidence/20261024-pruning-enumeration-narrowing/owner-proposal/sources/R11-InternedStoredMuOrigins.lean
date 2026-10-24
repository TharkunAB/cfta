import MicroCFTA.InternedNestedMissReadback
import MicroCFTA.InternedShallowHeap
import MicroCFTA.InternedUnionNormalForm
import MicroCFTA.InternedUnionNonemptyMembers
import MicroCFTA.InternedNonemptyRecords
import MicroCFTA.InternedLiveEdges

/-!
# Original source calls for complete stored Mu records

An origin records the actual expression, lexical inputs, two normalized
probe calls, fresh reservation, and normalized body call. The origin also
retains the source record invariants at the initial call. Ordinary effects
and cache hits preserve earlier origins.
-/
namespace MicroCFTA.InternedStoredMuOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedMissReadback
open InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedLiveEdges InternedUnionNormalForm InternedNonemptyRecords InternedUnionNonemptyMembers
open InternedBinderProtocol (Reference NodeKey)

/-- These independently derived source invariants justify every primitive normalization branch. -/
structure Normal (state : State Symbol Guard) : Prop where
  facts : Facts state
  live : Live state
  flat : Flat state
  proper : NonemptyRecords state
  members : MembersNonempty state

/-- Empty source caches satisfy all primitive normalization invariants. -/
theorem empty_normal : Normal (empty (Symbol := Symbol) (Guard := Guard)) :=
  ⟨empty_facts, empty_live, empty_flat, empty_nonempty, empty_membersNonempty⟩

/-- Arbitrary nested source execution preserves the normalization facts on done and pending outcomes. -/
theorem build_normal [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) : Normal (build expression environment state).state :=
  ⟨(build_verified expression environment state normal.facts inputs).facts,
    build_live expression environment state normal.live,
    build_flat expression environment state normal.facts inputs normal.flat,
    build_nonempty expression environment state normal.proper,
    build_membersNonempty expression environment state normal.facts inputs normal.members⟩

/-- Actual normalized callbacks preserve complete source provenance for their returned value. -/
theorem callback_verified [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state (.reference name :: environment)) :
    Verified state (callback expression environment name state) Available :=
  bind_verified state _ _ Available Available (build_verified expression _ state facts inputs)
    (fun value after _ afterFacts available => filter_verified name value after afterFacts available)

/-- Normalized callbacks retain the actual source record invariants at their stopping state. -/
theorem callback_normal [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment)) :
    Normal (callback expression environment name state).state := by
  have checked := build_verified expression _ state normal.facts inputs
  have built := build_normal expression _ state normal inputs
  cases returned : build expression (.reference name :: environment) state with
  | pending key after => simpa only [callback, returned, Outcome.bind, Outcome.state] using built
  | done value after =>
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using built
      have available := checked.result value after returned
      simp only [callback, returned, Outcome.bind]
      exact ⟨(filter_verified name value after afterNormal.facts available).facts,
        filter_live name value after afterNormal.live,
        filter_flat name value after afterNormal.flat available,
        filter_nonempty name value after afterNormal.proper,
        filter_membersNonempty name value after afterNormal.members available⟩

/-- Reserving an identity leaves all complete source payload invariants unchanged. -/
theorem reserve_normal (key : NodeKey) (state : State Symbol Guard) (normal : Normal state) :
    Normal {state with nodes := (Cache.intern state.nodes key).2} :=
  ⟨reserve_facts key state normal.facts, normal.live, normal.flat, normal.proper, normal.members⟩

/-- A complete payload keeps the exact original calls that produced its two probes and its fresh body. -/
def Origin [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) : Prop :=
  ∃ expression environment before afterDepth afterOrdinary afterBody,
    Normal before ∧ Values before environment ∧
    callback expression environment .depth before = .done depth afterDepth ∧
    callback expression environment (.uninterned depth.depth) afterDepth = .done ordinary afterOrdinary ∧
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

/-- Root filtering introduces no complete Mu payload. -/
theorem filter_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) : NoNewMu state (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact noNewMu_refl state
  case union => split
                · exact makeUnion_noNewMu _ state
                · exact noNewMu_refl state

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

/-- The actual reserved local is absent from every captured free set after the two original probes. -/
theorem probes_fresh [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before afterDepth afterOrdinary : State Symbol Guard)
    (depth ordinary : Value Symbol Guard) (facts : Facts before) (inputs : Values before environment)
    (depthDone : callback expression environment .depth before = .done depth afterDepth)
    (ordinaryDone : callback expression environment (.uninterned depth.depth) afterDepth = .done ordinary afterOrdinary)
    (missing : afterOrdinary.nodes.table (muKey depth ordinary) = none) :
    ∀ value ∈ environment,
      .interned (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1.identity ∉ value.free := by
  have firstInputs : Values before (.reference .depth :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact depth_available before
    · exact inputs value member
  have first := callback_verified expression environment .depth before facts firstInputs
  have afterFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using first.facts
  have afterInputs : Values afterDepth environment := by
    intro value member
    simpa only [depthDone, Outcome.state] using first.available value (inputs value member)
  have secondInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ordinary_available afterDepth depth.depth
    · exact afterInputs value member
  have second := callback_verified expression environment (.uninterned depth.depth) afterDepth afterFacts secondInputs
  have finalFacts : Facts afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using second.facts
  intro value member
  have available : Available afterOrdinary value := by
    simpa only [ordinaryDone, Outcome.state] using second.available value (afterInputs value member)
  rw [intern_miss_identity afterOrdinary.nodes _ missing]
  exact next_absent afterOrdinary.nodes finalFacts.coherent.valid.2 value available.issued

end MicroCFTA.InternedStoredMuOrigins
