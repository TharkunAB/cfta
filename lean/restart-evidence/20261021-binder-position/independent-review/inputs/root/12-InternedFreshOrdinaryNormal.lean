import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedNestedMuOrigins

/-!
# Normalization invariants for repaired nested construction

The repaired executor preserves the existing primitive normalization facts.
The proof follows its actual chosen ordinary names and all intermediate effects.
It permits pending outcomes and does not assert general completion.
-/
namespace MicroCFTA.InternedFreshOrdinaryNormal
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedFacts InternedNestedRequestFacts InternedConstructionProvenance
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedFreshProbeKeys InternedEdgeResidency
open InternedStoredMuOrigins (Normal empty_normal reserve_normal)
open InternedLiveEdges InternedUnionNormalForm InternedNonemptyRecords InternedUnionNonemptyMembers
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)

/-- Sequential execution retains all primitive invariants at its stopping state. -/
theorem bind_normal (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (normal : Normal outcome.state)
    (later : ∀ value after, outcome = .done value after → Normal after → Normal (next value after).state) :
    Normal (outcome.bind next).state := by
  cases outcome with
  | pending => exact normal
  | done value after => exact later value after rfl normal

/-- Filtering a completed callback uses only the available input record. -/
theorem filter_normal [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    Normal (work (withoutSelfReference name value) state).state :=
  ⟨(filter_verified name value state normal.facts available).facts,
    filter_live name value state normal.live, filter_flat name value state normal.flat available,
    filter_nonempty name value state normal.proper, filter_membersNonempty name value state normal.members available⟩

/-- A Mu request retains normalization through its actual reserved body call. -/
theorem request_normal [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (call : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (normal : Normal state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (checked : ∀ name current, Grows state current → Extends state.nodes.issued current.nodes.issued →
      Normal current → Available current (.reference name) →
      Verified current (call name current) Available ∧ Normal (call name current).state) :
    Normal (request smart depth ordinary call state).state := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, present, Outcome.state] using normal
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have growth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends state.nodes key normal.facts.coherent.valid.2
      have built := checked (.interned entry.1.identity) allocated growth history (reserve_normal key state normal)
        (reserve_available key state normal.facts.coherent normal.facts.cached).2
      simp only [request, installed]
      change Normal ((call (.interned entry.1.identity) allocated).bind
        (fun body after => complete smart entry.1 body depth ordinary after)).state
      apply bind_normal _ _ built.2
      intro body after returned afterNormal
      have bodyAvailable := built.1.result body after returned
      have laterGrowth : Grows allocated after := by simpa only [returned, Outcome.state] using built.1.growth
      have laterHistory : Extends allocated.nodes.issued after.nodes.issued := by
        simpa only [returned, Outcome.state] using built.1.history
      have stored : after.nodes.table key = some entry.1 := laterGrowth.nodes key entry.1
        (Cache.intern_correct state.nodes key normal.facts.coherent.valid.2).2.1
      have depthLater := depthAvailable.grows state after (grows_trans growth laterGrowth) (extends_trans history laterHistory)
      have ordinaryLater := ordinaryAvailable.grows state after (grows_trans growth laterGrowth) (extends_trans history laterHistory)
      exact ⟨(complete_verified smart entry.1 body depth ordinary after afterNormal.facts stored bodyAvailable depthLater ordinaryLater).facts,
        complete_live smart entry.1 body depth ordinary after afterNormal.live,
        complete_flat smart entry.1 body depth ordinary after afterNormal.flat,
        complete_nonempty smart entry.1 body depth ordinary after afterNormal.proper,
        complete_membersNonempty smart entry.1 body depth ordinary after afterNormal.members⟩

mutual
/-- Every repaired expression preserves the primitive normalization invariants. -/
theorem build_normal [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) : Normal (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using normal
  | node edges =>
      have verified := buildEdges_verified edges environment state normal.facts inputs
      rw [build]
      apply bind_normal _ _ (buildEdges_normal edges environment state normal inputs)
      intro values after returned afterNormal
      exact ⟨(node_verified values after afterNormal.facts (verified.result values after returned)).facts,
        makeNode_live values after afterNormal.live, makeNode_flat values after afterNormal.flat,
        makeNode_nonempty values after afterNormal.proper, makeNode_membersNonempty values after afterNormal.members⟩
  | union members =>
      have verified := buildMany_verified members environment state normal.facts inputs
      rw [build]
      apply bind_normal _ _ (buildMany_normal members environment state normal inputs)
      intro values after returned afterNormal
      have available := verified.result values after returned
      exact ⟨(union_verified values after afterNormal.facts available).facts,
        makeUnion_live values after afterNormal.live, makeUnion_flat values after afterNormal.flat available,
        makeUnion_nonempty values after afterNormal.proper, makeUnion_membersNonempty values after afterNormal.members available⟩
  | binder smart body =>
      have checked : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
          Verified current (callback body environment name current) Available ∧ Normal (callback body environment name current).state := by
        intro name current currentNormal currentInputs argument
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact argument
          · exact currentInputs value present
        refine ⟨callback_verified body environment name current currentNormal.facts withLocal, ?_⟩
        unfold callback
        apply bind_normal _ _ (build_normal body _ current currentNormal withLocal)
        intro value after returned afterNormal
        exact filter_normal name value after afterNormal
          ((build_verified body _ current currentNormal.facts withLocal).result value after returned)
      have first := checked .depth state normal inputs (depth_available state)
      rw [build]
      change Normal ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary).state
      apply bind_normal _ _ first.2
      intro depth afterDepth depthDone depthNormal
      have depthInputs : Values afterDepth environment := by
        intro value member
        simpa only [depthDone, Outcome.state] using first.1.available value (inputs value member)
      have second := checked (.uninterned (ordinaryLevel depth)) afterDepth depthNormal depthInputs
        (ordinary_available afterDepth (ordinaryLevel depth))
      apply bind_normal _ _ second.2
      intro ordinary afterOrdinary ordinaryDone ordinaryNormal
      have finalDepth : Available afterOrdinary depth := by
        simpa only [ordinaryDone, Outcome.state] using second.1.available depth (first.1.result depth afterDepth depthDone)
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa only [ordinaryDone, Outcome.state] using second.1.available value (depthInputs value member)
      apply request_normal smart depth ordinary _ afterOrdinary ordinaryNormal finalDepth (second.1.result ordinary afterOrdinary ordinaryDone)
      intro name current growth history currentNormal argument
      exact checked name current currentNormal
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history) argument
termination_by sizeOf expression

/-- Ordered repaired child computations preserve normalization at each intermediate cache. -/
theorem buildMany_normal [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) : Normal (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using normal
  | cons first rest =>
      have verified := build_verified first environment state normal.facts inputs
      rw [buildMany]
      apply bind_normal _ _ (build_normal first environment state normal inputs)
      intro value after returned afterNormal
      have afterInputs : Values after environment := by
        intro captured member
        simpa only [returned, Outcome.state] using verified.available captured (inputs captured member)
      exact bind_normal _ _ (buildMany_normal rest environment after afterNormal afterInputs)
        (fun _ _ _ finalNormal => finalNormal)
termination_by sizeOf expressions

/-- Ordered repaired edge computations preserve all primitive normalization facts. -/
theorem buildEdges_normal [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) : Normal (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using normal
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have verified := buildMany_verified children environment state normal.facts inputs
          rw [buildEdges]
          apply bind_normal _ _ (buildMany_normal children environment state normal inputs)
          intro values after returned afterNormal
          have available := verified.result values after returned
          have edgeNormal := InternedNestedMuOrigins.edge_normal symbol constraint values after afterNormal available
          have edgeVerified := edge_verified symbol constraint values after afterNormal.facts available
          apply bind_normal (work (makeEdge symbol constraint values) after) _ edgeNormal
          intro edge afterEdge edgeDone afterEdgeNormal
          have afterInputs : Values afterEdge environment := by
            intro captured member
            have middle : Available after captured := by
              simpa only [returned, Outcome.state] using verified.available captured (inputs captured member)
            simpa only [edgeDone, Outcome.state] using edgeVerified.available captured middle
          exact bind_normal _ _ (buildEdges_normal rest environment afterEdge afterEdgeNormal afterInputs)
            (fun _ _ _ finalNormal => finalNormal)
termination_by sizeOf expressions
end

/-- The repaired normalized callback preserves primitive normalization. -/
theorem callback_normal [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment)) :
    Normal (callback expression environment name state).state := by
  unfold callback
  apply bind_normal _ _ (build_normal expression _ state normal inputs)
  intro value after returned afterNormal
  exact filter_normal name value after afterNormal
    ((build_verified expression _ state normal.facts inputs).result value after returned)

/-- Empty-cache repaired construction establishes all primitive normalization facts. -/
theorem closed_normal [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Normal (build expression [] empty).state :=
  build_normal expression [] empty empty_normal (by intro value member; cases member)

end MicroCFTA.InternedFreshOrdinaryNormal
