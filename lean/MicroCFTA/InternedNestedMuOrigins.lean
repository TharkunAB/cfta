import MicroCFTA.InternedStoredMuOrigins

/-!
# Full nested source execution derives stored Mu origins

The proof follows both source probes before each recursive request. A miss
adds the original fresh-body call. A hit retains the earlier origin.
Pending outcomes retain origins for every record that already completed.
-/
namespace MicroCFTA.InternedNestedMuOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedMissReadback
open InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap InternedStoredMuOrigins
open InternedConstructionProvenance
open InternedLiveEdges InternedUnionNormalForm InternedNonemptyRecords InternedUnionNonemptyMembers
open InternedBinderProtocol (Reference NodeKey)

/-- Ordered source children retain all normalization facts at their actual stopping state. -/
theorem buildMany_normal [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) : Normal (buildMany expressions environment state).state :=
  ⟨(buildMany_verified expressions environment state normal.facts inputs).facts,
    buildMany_live expressions environment state normal.live,
    buildMany_flat expressions environment state normal.facts inputs normal.flat,
    buildMany_nonempty expressions environment state normal.proper,
    buildMany_membersNonempty expressions environment state normal.facts inputs normal.members⟩

/-- Ordered source edges retain all normalization facts at their actual stopping state. -/
theorem buildEdges_normal [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) : Normal (buildEdges expressions environment state).state :=
  ⟨(buildEdges_verified expressions environment state normal.facts inputs).facts,
    buildEdges_live expressions environment state normal.live,
    buildEdges_flat expressions environment state normal.facts inputs normal.flat,
    buildEdges_nonempty expressions environment state normal.proper,
    buildEdges_membersNonempty expressions environment state normal.facts inputs normal.members⟩

/-- Constructing one edge changes no complete node payload invariant. -/
theorem edge_normal [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state values) : Normal (run (makeEdge symbol constraint values) state).2 :=
  ⟨(edge_verified symbol constraint values state normal.facts inputs).facts,
    normal.live, normal.flat, normal.proper, normal.members⟩

mutual
/-- Every stored Mu after arbitrary source execution has its actual original probe and fresh-body calls. -/
theorem build_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (heap : Heap state) :
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
      have checked : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
          Heap current → Heap (callback body environment name current).state := by
        intro name current currentNormal currentInputs argument currentHeap
        have all : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentInputs value member
        exact bind_heap _ _ (build_origins body _ current currentNormal all currentHeap)
          (fun value after _ afterHeap => preserve after _ afterHeap (filter_noNewMu name value after))
      have depthInputs : Values state (.reference .depth :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact depth_available state
        · exact inputs value member
      have depthNormal := callback_normal body environment .depth state normal depthInputs
      have depthVerified := callback_verified body environment .depth state normal.facts depthInputs
      rw [build]
      change Heap ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary).state
      apply bind_heap _ _ (checked .depth state normal inputs (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap
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
      have ordinaryVerified := callback_verified body environment (.uninterned depth.depth) afterDepth depthFacts.facts ordinaryInputs
      apply bind_heap _ _ (checked (.uninterned depth.depth) afterDepth depthFacts afterInputs
        (ordinary_available afterDepth depth.depth) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap
      have ordinaryFacts : Normal afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryNormal
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
          have reserved : Normal allocated := reserve_normal (muKey depth ordinary) afterOrdinary ordinaryFacts
          have growth : Grows afterOrdinary allocated :=
            ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
          have history := intern_issued_extends afterOrdinary.nodes (muKey depth ordinary) ordinaryFacts.facts.coherent.valid.2
          have allocatedInputs : Values allocated environment :=
            fun value member => (finalInputs value member).grows afterOrdinary allocated growth history
          have freshAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
            (reserve_available (muKey depth ordinary) afterOrdinary ordinaryFacts.facts.coherent ordinaryFacts.facts.cached).2
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
    (normal : Normal state) (inputs : Values state environment) (heap : Heap state) :
    Heap (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      have checked := build_verified first environment state normal.facts inputs
      have normalAfter := build_normal first environment state normal inputs
      rw [buildMany]
      apply bind_heap _ _ (build_origins first environment state normal inputs heap)
      intro value after returned afterHeap
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using normalAfter
      have afterInputs : Values after environment := by
        intro value member
        simpa only [returned, Outcome.state] using checked.available value (inputs value member)
      exact bind_heap _ _ (buildMany_origins rest environment after afterNormal afterInputs afterHeap)
        (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions

/-- Actual edge allocation and ordered siblings preserve every earlier recursive construction witness. -/
theorem buildEdges_origins [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (heap : Heap state) :
    Heap (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have checked := buildMany_verified children environment state normal.facts inputs
          have normalAfter := buildMany_normal children environment state normal inputs
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_origins children environment state normal inputs heap)
          intro values after returned afterHeap
          have afterNormal : Normal after := by simpa only [returned, Outcome.state] using normalAfter
          have afterInputs : Values after environment := by
            intro value member
            simpa only [returned, Outcome.state] using checked.available value (inputs value member)
          have available := checked.result values after returned
          let result := run (makeEdge symbol constraint values) after
          have edgeNormal : Normal result.2 := edge_normal symbol constraint values after afterNormal available
          have edgeInputs : Values result.2 environment :=
            fun value member => available_after_run (makeEdge symbol constraint values) after afterNormal.facts.coherent.valid (afterInputs value member)
          change Heap ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (buildEdges_origins rest environment result.2 edgeNormal edgeInputs afterHeap)
            (fun _ _ _ laterHeap => laterHeap)
termination_by sizeOf expressions
end

/-- All complete recursive payloads in a first closed source run have actual construction origins, even if the run is pending. -/
theorem closed_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  build_origins expression [] empty empty_normal (by intro value member; cases member) empty_heap

end MicroCFTA.InternedNestedMuOrigins
