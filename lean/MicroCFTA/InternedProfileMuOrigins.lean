import MicroCFTA.InternedNestedMuOrigins
import MicroCFTA.InternedNestedProfiles

/-!
# Stored Mu origins retain the verified original profile table

The original call starts with the profile invariant already established.
Full source execution preserves that invariant at each probe and fresh
body call. This permits later use of the actual historical callback trace
without an assumed profile property for its original cache.
-/
namespace MicroCFTA.InternedProfileMuOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedMissReadback
open InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap InternedStoredMuOrigins
open InternedConstructionProvenance InternedNestedMuOrigins InternedNestedProfiles InternedProfileExecutionFacts
open InternedBinderProtocol (Reference NodeKey)

/-- Each original recursive call starts with an independently verified decoded-profile table. -/
def Origin [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) : Prop :=
  ∃ expression environment before afterDepth afterOrdinary afterBody,
    Normal before ∧ Values before environment ∧ InternedProfileHeap.Heap before ∧
    callback expression environment .depth before = .done depth afterDepth ∧
    callback expression environment (.uninterned depth.depth) afterDepth = .done ordinary afterOrdinary ∧
    afterOrdinary.nodes.table (muKey depth ordinary) = none ∧
    entry = (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1 ∧
    callback expression environment (.interned entry.identity)
      {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2} = .done body afterBody

/-- Every completed recursive payload has a verified original prefix and its exact three source calls. -/
def Origins [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Origin entry body depth ordinary

/-- The stronger witness retains every field of the earlier source origin. -/
theorem forget [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : Origin entry body depth ordinary) :
    InternedStoredMuOrigins.Origin entry body depth ordinary := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody, normal, inputs, _, calls⟩ := origin
  exact ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody, normal, inputs, calls⟩

/-- Original normalized callbacks retain the decoded-profile table on both outcomes. -/
theorem callback_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment)) (heap : InternedProfileHeap.Heap state) :
    InternedProfileHeap.Heap (callback expression environment name state).state := by
  exact (callback_checked expression environment name state normal inputs
    (by simpa only [List.map_cons, InternedRootProfile.profile] using build_profile expression _ state normal inputs heap)).heap

/-- Ordinary effects retain the exact verified source prefix of each earlier recursive payload. -/
theorem preserve [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (origins : Origins before) (old : NoNewMu before after) : Origins after := by
  intro key entry body depth ordinary stored
  exact origins key entry body depth ordinary (old key entry body depth ordinary stored)

/-- Sequencing retains origins at each actual stopping state. -/
theorem bind_heap [DecidableEq (EdgeKey Symbol Guard)] (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (origins : Origins outcome.state) (later : ∀ value after, outcome = .done value after → Origins after → Origins (next value after).state) :
    Origins (outcome.bind next).state := by
  cases outcome with
  | pending => exact origins
  | done value after => exact later value after rfl origins

/-- Completion adds the candidate's verified origin or retains an immutable earlier payload. -/
theorem complete_heap [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (origins : Origins state) (origin : Origin entry body depth ordinary) : Origins (complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact origins key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact origin

mutual
/-- Every stored Mu after arbitrary source execution has its actual original probe and fresh-body calls. -/
theorem build_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (decoded : InternedProfileHeap.Heap state) (heap : Origins state) :
    Origins (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using heap
  | node edges =>
      rw [build]
      exact bind_heap _ _ (buildEdges_origins edges environment state normal inputs decoded heap)
        (fun values after _ afterOrigins => preserve after _ afterOrigins (makeNode_noNewMu values after))
  | union members =>
      rw [build]
      exact bind_heap _ _ (buildMany_origins members environment state normal inputs decoded heap)
        (fun values after _ afterOrigins => preserve after _ afterOrigins (makeUnion_noNewMu values after))
  | binder smart body =>
      have checked : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
          InternedProfileHeap.Heap current → Origins current → Origins (callback body environment name current).state := by
        intro name current currentNormal currentInputs argument currentDecoded currentOrigins
        have all : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentInputs value member
        exact bind_heap _ _ (build_origins body _ current currentNormal all currentDecoded currentOrigins)
          (fun value after _ afterOrigins => preserve after _ afterOrigins (filter_noNewMu name value after))
      have depthInputs : Values state (.reference .depth :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact depth_available state
        · exact inputs value member
      have depthNormal := callback_normal body environment .depth state normal depthInputs
      have depthDecoded := callback_heap body environment .depth state normal depthInputs decoded
      have depthVerified := callback_verified body environment .depth state normal.facts depthInputs
      rw [build]
      change Origins ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary).state
      apply bind_heap _ _ (checked .depth state normal inputs (depth_available state) decoded heap)
      intro depth afterDepth depthDone depthOrigins
      have afterDecoded : InternedProfileHeap.Heap afterDepth := by simpa only [depthDone, Outcome.state] using depthDecoded
      have depthFacts : Normal afterDepth := by simpa only [depthDone, Outcome.state] using depthNormal
      have afterInputs : Values afterDepth environment := by
        intro value member
        simpa only [depthDone, Outcome.state] using depthVerified.available value (inputs value member)
      have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact ordinary_available afterDepth depth.depth
        · exact afterInputs value member
      have ordinaryNormal := callback_normal body environment (.uninterned depth.depth) afterDepth depthFacts ordinaryInputs
      have ordinaryDecoded := callback_heap body environment (.uninterned depth.depth) afterDepth depthFacts ordinaryInputs afterDecoded
      have ordinaryVerified := callback_verified body environment (.uninterned depth.depth) afterDepth depthFacts.facts ordinaryInputs
      apply bind_heap _ _ (checked (.uninterned depth.depth) afterDepth depthFacts afterInputs
        (ordinary_available afterDepth depth.depth) afterDecoded depthOrigins)
      intro ordinary afterOrdinary ordinaryDone ordinaryOrigins
      have finalDecoded : InternedProfileHeap.Heap afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryDecoded
      have ordinaryFacts : Normal afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryNormal
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available value (afterInputs value member)
      cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
      | some entry =>
          cases present : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
            simpa only [request, found, present, Outcome.state] using ordinaryOrigins
      | none =>
          let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
          let allocated := {afterOrdinary with nodes := entry.2}
          have reserved : Normal allocated := reserve_normal (muKey depth ordinary) afterOrdinary ordinaryFacts
          have growth : Grows afterOrdinary allocated :=
            ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
          have history := intern_issued_extends afterOrdinary.nodes (muKey depth ordinary) ordinaryFacts.facts.coherent.valid.2
          have allocatedInputs : Values allocated environment :=
            fun value member => (finalInputs value member).grows afterOrdinary allocated growth history
          have freshAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
            (reserve_available (muKey depth ordinary) afterOrdinary ordinaryFacts.facts.coherent ordinaryFacts.facts.cached).2
          have allocatedOrigins : Origins allocated := ordinaryOrigins
          have allocatedDecoded : InternedProfileHeap.Heap allocated := finalDecoded
          have actualOrigins := checked (.interned entry.1.identity) allocated reserved allocatedInputs freshAvailable allocatedDecoded allocatedOrigins
          simp only [request, found]
          change Origins ((callback body environment (.interned entry.1.identity) allocated).bind
            (fun value after => complete smart entry.1 value depth ordinary after)).state
          apply bind_heap _ _ actualOrigins
          intro actual afterBody actualDone afterOrigins
          exact complete_heap smart entry.1 actual depth ordinary afterBody afterOrigins
            ⟨body, environment, state, afterDepth, afterOrdinary, afterBody, normal, inputs, decoded,
              depthDone, ordinaryDone, found, rfl, actualDone⟩
termination_by sizeOf expression

/-- Ordered source child construction preserves all complete recursive origins. -/
theorem buildMany_origins [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (decoded : InternedProfileHeap.Heap state) (heap : Origins state) :
    Origins (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      have checked := build_verified first environment state normal.facts inputs
      have normalAfter := build_normal first environment state normal inputs
      have decodedAfter := (build_profile first environment state normal inputs decoded).heap
      rw [buildMany]
      apply bind_heap _ _ (build_origins first environment state normal inputs decoded heap)
      intro value after returned afterOrigins
      have afterDecoded : InternedProfileHeap.Heap after := by simpa only [returned, Outcome.state] using decodedAfter
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using normalAfter
      have afterInputs : Values after environment := by
        intro value member
        simpa only [returned, Outcome.state] using checked.available value (inputs value member)
      exact bind_heap _ _ (buildMany_origins rest environment after afterNormal afterInputs afterDecoded afterOrigins)
        (fun _ _ _ laterOrigins => laterOrigins)
termination_by sizeOf expressions

/-- Actual edge allocation and ordered siblings preserve every earlier recursive construction witness. -/
theorem buildEdges_origins [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (decoded : InternedProfileHeap.Heap state) (heap : Origins state) :
    Origins (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have checked := buildMany_verified children environment state normal.facts inputs
          have normalAfter := buildMany_normal children environment state normal inputs
          have decodedAfter := (buildMany_profile children environment state normal inputs decoded).heap
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_origins children environment state normal inputs decoded heap)
          intro values after returned afterOrigins
          have afterDecoded : InternedProfileHeap.Heap after := by simpa only [returned, Outcome.state] using decodedAfter
          have afterNormal : Normal after := by simpa only [returned, Outcome.state] using normalAfter
          have afterInputs : Values after environment := by
            intro value member
            simpa only [returned, Outcome.state] using checked.available value (inputs value member)
          have available := checked.result values after returned
          let result := run (makeEdge symbol constraint values) after
          have edgeNormal : Normal result.2 := edge_normal symbol constraint values after afterNormal available
          have edgeInputs : Values result.2 environment :=
            fun value member => available_after_run (makeEdge symbol constraint values) after afterNormal.facts.coherent.valid (afterInputs value member)
          change Origins ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (buildEdges_origins rest environment result.2 edgeNormal edgeInputs afterDecoded afterOrigins)
            (fun _ _ _ laterOrigins => laterOrigins)
termination_by sizeOf expressions
end

/-- Every complete recursive payload after a first closed run has a verified original source prefix. -/
theorem closed_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Origins (build expression [] empty).state :=
  build_origins expression [] empty empty_normal (by intro value member; cases member)
    InternedProfileHeap.empty_heap (by intro key entry body depth ordinary impossible; cases impossible)

end MicroCFTA.InternedProfileMuOrigins
