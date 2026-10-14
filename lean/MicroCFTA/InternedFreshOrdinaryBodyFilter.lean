import MicroCFTA.InternedFreshOrdinaryNormal
import MicroCFTA.InternedStoredBodyInvariant

/-!
# Actual stored body filters in the repaired executor

Each callback applies the source root self-reference filter. The repaired
ordinary probe choice preserves this property through both probes, fresh
allocation, and complete cache hits. The statement also covers a pending
outer request and arbitrary available lexical inputs.
-/
namespace MicroCFTA.InternedFreshOrdinaryBodyFilter
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedFacts InternedNestedRequestFacts
open InternedConstructionProvenance
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedFreshProbeKeys InternedStoredSelfFilter InternedUnionNormalForm
open InternedStoredMuOrigins (Normal empty_normal reserve_normal)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryNormal
open InternedBinderProtocol (Reference NodeKey)

/-- Actual reservation retains earlier filters and installs the filtered fresh body. -/
theorem request_filtered [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (call : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (normal : Normal state) (clean : Clean state)
    (checked : ∀ name current, Grows state current → Extends state.nodes.issued current.nodes.issued →
      Normal current → Available current (.reference name) → Clean current →
      Verified current (call name current) (fun state value => Available state value ∧ NoSelf name value) ∧
      Clean (call name current).state) :
    Clean (request smart depth ordinary call state).state := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, present, Outcome.state] using clean
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have growth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends state.nodes key normal.facts.coherent.valid.2
      have body := checked (.interned entry.1.identity) allocated growth history (reserve_normal key state normal)
        (reserve_available key state normal.facts.coherent normal.facts.cached).2 clean
      simp only [request, installed]
      exact bind_clean allocated _ _ _ body.1 body.2
        (fun value after _ _ property afterClean => complete_clean smart entry.1 value depth ordinary after afterClean property.2)

mutual
/-- Repaired source construction retains the actual root filter of every complete stored Mu. -/
theorem build_clean [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (clean : Clean state) :
    Clean (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using clean
  | node edges =>
      rw [build]
      exact bind_clean state _ _ Edges (buildEdges_verified edges environment state normal.facts inputs)
        (buildEdges_clean edges environment state normal inputs clean)
        (fun values after _ _ _ afterClean => makeNode_clean values after afterClean)
  | union members =>
      rw [build]
      exact bind_clean state _ _ Values (buildMany_verified members environment state normal.facts inputs)
        (buildMany_clean members environment state normal inputs clean)
        (fun values after _ _ _ afterClean => makeUnion_clean values after afterClean)
  | binder smart body =>
      have checked : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
          Clean current → Verified current (callback body environment name current)
            (fun state value => Available state value ∧ NoSelf name value) ∧
          Clean (callback body environment name current).state := by
        intro name current currentNormal currentInputs argument currentClean
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact argument
          · exact currentInputs value present
        have verified := build_verified body _ current currentNormal.facts withLocal
        have preserved := build_normal body _ current currentNormal withLocal
        constructor
        · unfold callback
          apply bind_verified current _ _ Available (fun state value => Available state value ∧ NoSelf name value) verified
          intro value after returned afterFacts available
          have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
          have filtered := filter_verified name value after afterFacts available
          refine ⟨filtered.facts, filtered.growth, filtered.history, ?_⟩
          intro result final completed
          have equal : (run (withoutSelfReference name value) after).1 = result := (Outcome.done.inj completed).1
          exact ⟨filtered.result result final completed,
            equal ▸ filter_noSelf name value after afterFacts.coherent afterFacts.cached afterNormal.flat available⟩
        · unfold callback
          exact bind_clean current _ _ Available verified (build_clean body _ current currentNormal withLocal currentClean)
            (fun value after _ _ _ afterClean => filter_clean name value after afterClean)
      have first := checked .depth state normal inputs (depth_available state) clean
      rw [build]
      change Clean ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary).state
      apply bind_clean state _ _ _ first.1 first.2
      intro depth afterDepth depthDone _ _ depthClean
      have depthNormal : Normal afterDepth := by
        simpa only [depthDone, Outcome.state] using callback_normal body environment .depth state normal
          (by intro value member; rcases List.mem_cons.mp member with rfl | present
              · exact depth_available state
              · exact inputs value present)
      have depthInputs : Values afterDepth environment := by
        intro value member
        simpa only [depthDone, Outcome.state] using first.1.available value (inputs value member)
      have second := checked (.uninterned (ordinaryLevel depth)) afterDepth depthNormal depthInputs
        (ordinary_available afterDepth (ordinaryLevel depth)) depthClean
      apply bind_clean afterDepth _ _ _ second.1 second.2
      intro ordinary afterOrdinary ordinaryDone _ _ ordinaryClean
      have ordinaryNormal : Normal afterOrdinary := by
        simpa only [ordinaryDone, Outcome.state] using callback_normal body environment
          (.uninterned (ordinaryLevel depth)) afterDepth depthNormal
          (by intro value member; rcases List.mem_cons.mp member with rfl | present
              · exact ordinary_available afterDepth (ordinaryLevel depth)
              · exact depthInputs value present)
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa only [ordinaryDone, Outcome.state] using second.1.available value (depthInputs value member)
      apply request_filtered smart depth ordinary _ afterOrdinary ordinaryNormal ordinaryClean
      intro name current growth history currentNormal argument currentClean
      exact checked name current currentNormal
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history) argument currentClean
termination_by sizeOf expression

/-- Each ordered repaired child computation preserves earlier complete body filters. -/
theorem buildMany_clean [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (clean : Clean state) :
    Clean (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using clean
  | cons first rest =>
      have head := build_verified first environment state normal.facts inputs
      rw [buildMany]
      apply bind_clean state _ _ Available head (build_clean first environment state normal inputs clean)
      intro value afterHead returned headFacts _ headClean
      have laterInputs : Values afterHead environment := by
        intro value member
        simpa only [returned, Outcome.state] using head.available value (inputs value member)
      have laterNormal : Normal afterHead := by
        simpa only [returned, Outcome.state] using build_normal first environment state normal inputs
      exact bind_clean afterHead _ _ Values (buildMany_verified rest environment afterHead headFacts laterInputs)
        (buildMany_clean rest environment afterHead laterNormal laterInputs headClean)
        (fun values afterTail _ _ _ tailClean => tailClean)
termination_by sizeOf expressions

/-- Repaired edge schedules preserve filters through child allocation and later siblings. -/
theorem buildEdges_clean [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (clean : Clean state) :
    Clean (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using clean
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childrenBuilt := buildMany_verified children environment state normal.facts inputs
          rw [buildEdges]
          apply bind_clean state _ _ Values childrenBuilt (buildMany_clean children environment state normal inputs clean)
          intro values afterChildren childrenReturned childrenFacts valuesAvailable childrenClean
          have edgeBuilt := edge_verified symbol constraint values afterChildren childrenFacts valuesAvailable
          apply bind_clean afterChildren _ _ InternedEdgeResidency.EdgeResident edgeBuilt childrenClean
          intro edge afterEdge edgeReturned edgeFacts _ edgeClean
          have childrenNormal : Normal afterChildren := by
            simpa only [childrenReturned, Outcome.state] using buildMany_normal children environment state normal inputs
          have laterNormal : Normal afterEdge := by
            cases edgeReturned
            exact InternedNestedMuOrigins.edge_normal symbol constraint values afterChildren childrenNormal valuesAvailable
          have laterInputs : Values afterEdge environment := by
            intro value member
            have intermediate : Available afterChildren value := by
              simpa only [childrenReturned, Outcome.state] using childrenBuilt.available value (inputs value member)
            simpa only [edgeReturned, Outcome.state] using edgeBuilt.available value intermediate
          exact bind_clean afterEdge _ _ Edges (buildEdges_verified rest environment afterEdge edgeFacts laterInputs)
            (buildEdges_clean rest environment afterEdge laterNormal laterInputs edgeClean)
            (fun edges afterTail _ _ _ tailClean => tailClean)
termination_by sizeOf expressions
end

/-- Empty-cache repaired execution derives every complete stored root filter. -/
theorem closed_clean [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Clean (build expression [] empty).state :=
  build_clean expression [] empty empty_normal (by intro value member; cases member) empty_clean

end MicroCFTA.InternedFreshOrdinaryBodyFilter
