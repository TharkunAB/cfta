import MicroCFTA.InternedStoredSelfFilter

/-!
# Source-derived stored Mu body normalization

The complete nested executor preserves the root self-reference invariant
through both probes, allocation, canonical lookup, and completion. This
supplies a strict stored-value unfolding law for the shallow Mu fragment.
-/
namespace MicroCFTA.InternedStoredBodyInvariant
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedTemplateProvenance InternedFreshProbeKeys
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedUnionNormalForm InternedStoredSelfFilter
open InternedPreparedSubstitution InternedShallowGate InternedGateRank

mutual
/-- Every nested source execution stores only actually filtered Mu bodies. -/
theorem build_clean [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (flat : Flat state) (clean : Clean state) :
    Clean (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using clean
  | node edges =>
      rw [build]
      exact bind_clean state _ _ Edges (buildEdges_verified edges environment state facts inputs)
        (buildEdges_clean edges environment state facts inputs flat clean)
        (fun values after _ _ _ afterClean => makeNode_clean values after afterClean)
  | union members =>
      rw [build]
      exact bind_clean state _ _ Values (buildMany_verified members environment state facts inputs)
        (buildMany_clean members environment state facts inputs flat clean)
        (fun values after _ _ _ afterClean => makeUnion_clean values after afterClean)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have callbackFlat : ∀ name current, Facts current → Values current environment → Available current (.reference name) → Flat current →
          Flat (callback name current).state := by
        intro name current currentFacts currentInputs localAvailable currentFlat
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        exact bind_flat current _ _ Available (build_verified body _ current currentFacts withLocal)
          (build_flat body _ current currentFacts withLocal currentFlat)
          (fun value after _ _ available afterFlat => filter_flat name value after afterFlat available)
      have checked : ∀ name current, Facts current → Values current environment → Available current (.reference name) → Flat current → Clean current →
          Verified current (callback name current) (fun state value => Available state value ∧ NoSelf name value) ∧ Clean (callback name current).state := by
        intro name current currentFacts currentInputs localAvailable currentFlat currentClean
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        have verified := build_verified body (.reference name :: environment) current currentFacts withLocal
        have flatBuilt := build_flat body (.reference name :: environment) current currentFacts withLocal currentFlat
        constructor
        · apply bind_verified current _ _ Available (fun state value => Available state value ∧ NoSelf name value) verified
          intro value after returned afterFacts available
          have afterFlat : Flat after := by simpa only [returned, Outcome.state] using flatBuilt
          have filtered := filter_verified name value after afterFacts available
          refine ⟨filtered.facts, filtered.growth, filtered.history, ?_⟩
          intro result final completed
          have original := filtered.result result final completed
          have equal : (run (withoutSelfReference name value) after).1 = result := by
            exact (Outcome.done.inj completed).1
          exact ⟨original, equal ▸ filter_noSelf name value after afterFacts.coherent afterFacts.cached afterFlat available⟩
        · exact bind_clean current _ _ Available verified (build_clean body _ current currentFacts withLocal currentFlat currentClean)
            (fun value after _ _ _ afterClean => filter_clean name value after afterClean)
      have depth := checked .depth state facts inputs (depth_available state) flat clean
      rw [build]
      change Clean ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_clean state _ _ _ depth.1 depth.2
      intro depthValue afterDepth returned depthFacts _ depthClean
      have depthInputs : Values afterDepth environment := by
        intro value member
        simpa [returned, Outcome.state] using depth.1.available value (inputs value member)
      have depthFlat : Flat afterDepth := by
        simpa [returned, Outcome.state] using callbackFlat .depth state facts inputs (depth_available state) flat
      have ordinary := checked (.uninterned depthValue.depth) afterDepth depthFacts depthInputs
        (ordinary_available afterDepth depthValue.depth) depthFlat depthClean
      apply bind_clean afterDepth _ _ _ ordinary.1 ordinary.2
      intro ordinaryValue afterOrdinary ordinaryReturned ordinaryFacts _ ordinaryClean
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa [ordinaryReturned, Outcome.state] using ordinary.1.available value (depthInputs value member)
      have ordinaryFlat : Flat afterOrdinary := by
        simpa [ordinaryReturned, Outcome.state] using callbackFlat (.uninterned depthValue.depth) afterDepth depthFacts depthInputs
          (ordinary_available afterDepth depthValue.depth) depthFlat
      apply request_clean smart depthValue ordinaryValue callback afterOrdinary ordinaryFacts ordinaryFlat ordinaryClean
      intro name current growth history currentFacts localAvailable currentFlat currentClean
      exact checked name current currentFacts
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history) localAvailable currentFlat currentClean
termination_by sizeOf expression

/-- The original ordered child schedule preserves all completed Mu body filters. -/
theorem buildMany_clean [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (flat : Flat state) (clean : Clean state) :
    Clean (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using clean
  | cons first rest =>
      have head := build_verified first environment state facts inputs
      rw [buildMany]
      apply bind_clean state _ _ Available head (build_clean first environment state facts inputs flat clean)
      intro value afterHead returned headFacts _ headClean
      have laterInputs : Values afterHead environment := by
        intro value member
        simpa [returned, Outcome.state] using head.available value (inputs value member)
      have laterFlat : Flat afterHead := by
        simpa [returned, Outcome.state] using build_flat first environment state facts inputs flat
      exact bind_clean afterHead _ _ Values (buildMany_verified rest environment afterHead headFacts laterInputs)
        (buildMany_clean rest environment afterHead headFacts laterInputs laterFlat headClean)
        (fun values afterTail _ _ _ tailClean => tailClean)
termination_by sizeOf expressions

/-- Child and edge effects cannot change completed Mu bodies. -/
theorem buildEdges_clean [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (flat : Flat state) (clean : Clean state) :
    Clean (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using clean
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childrenBuilt := buildMany_verified children environment state facts inputs
          rw [buildEdges]
          apply bind_clean state _ _ Values childrenBuilt (buildMany_clean children environment state facts inputs flat clean)
          intro values afterChildren childrenReturned childrenFacts valuesAvailable childrenClean
          have edgeBuilt := edge_verified symbol constraint values afterChildren childrenFacts valuesAvailable
          apply bind_clean afterChildren _ _ InternedEdgeResidency.EdgeResident edgeBuilt childrenClean
          intro edge afterEdge edgeReturned edgeFacts _ edgeClean
          have laterInputs : Values afterEdge environment := by
            intro value member
            have intermediate : Available afterChildren value := by
              simpa [childrenReturned, Outcome.state] using childrenBuilt.available value (inputs value member)
            simpa [edgeReturned, Outcome.state] using edgeBuilt.available value intermediate
          have childrenFlat : Flat afterChildren := by
            simpa [childrenReturned, Outcome.state] using buildMany_flat children environment state facts inputs flat
          have laterFlat : Flat afterEdge := by
            cases edgeReturned
            exact childrenFlat
          exact bind_clean afterEdge _ _ Edges (buildEdges_verified rest environment afterEdge edgeFacts laterInputs)
            (buildEdges_clean rest environment afterEdge edgeFacts laterInputs laterFlat edgeClean)
            (fun edges afterTail _ _ _ tailClean => tailClean)
termination_by sizeOf expressions
end

/-- Every completed Mu from empty-state source syntax has its actual filtered body. -/
theorem closed_clean [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Clean (build expression [] empty).state :=
  build_clean expression [] empty empty_facts (by intro value member; cases member) empty_flat empty_clean

/-- A shallow stored open Mu derives its root guard directly from source cache invariants. -/
theorem stored_guarded (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary)) (zero : body.depth = 0)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) : GuardedValue (.interned entry.identity) body := by
  have bodyAvailable : Available state body := available.children body (by simp [InternedProbeProvenance.children])
  have normalized := resident_clean state clean (.mu entry body depth ordinary) available.resident
  cases body with
  | empty => exact .empty
  | reference other =>
      apply GuardedValue.reference
      intro same
      simp [same, Value.free] at opened
  | node actual edges level free => exact .node actual edges level free
  | mu => simp [Value.depth] at zero
  | union actual members level free =>
      apply GuardedValue.union
      intro value member
      have atomic := resident_flat state flat (.union actual members level free) bodyAvailable.resident value member
      have bound := InternedUnionSeparation.child_depth state coherent _ value bodyAvailable member
      have childZero := Nat.eq_zero_of_le_zero (zero ▸ bound)
      apply atomic_guarded _ value atomic childZero
      intro same
      exact normalized (same ▸ member)

/-- Every available shallow open Mu in a source-derived state has an actual
prepared unfolding whose head rank strictly decreases. -/
theorem stored_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary)) (zero : body.depth = 0)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ template, prepare (.interned entry.identity) body = some template ∧
      headRank (run (compile template (.mu entry body depth ordinary)) state).1 <
        headRank (.mu entry body depth ordinary) :=
  shallow_unfold_decreases entry body depth ordinary state facts.coherent facts.cached available zero
    (stored_guarded entry body depth ordinary state facts.coherent flat clean available zero opened)

/-- Every completed source record from empty-cache execution supplies all
representation premises, even when another request later reports pending. -/
theorem built_record_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (key : InternedBinderProtocol.NodeKey)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (zero : body.depth = 0) (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ template, prepare (.interned entry.identity) body = some template ∧
      headRank (run (compile template (.mu entry body depth ordinary)) (build expression [] empty).state).1 <
        headRank (.mu entry body depth ordinary) := by
  have checked := closed_verified expression
  exact stored_unfold_decreases entry body depth ordinary _ checked.facts (closed_flat expression) (closed_clean expression)
    (checked.facts.cached.nodes key _ stored) zero opened

/-- An enclosing recursive node contains an open shallow Mu among its actual stored children. -/
def fixture : Syntax Nat Unit :=
  .binder true (.node [.mk 0 () [.binder true (.node [.mk 1 () [.var 0, .var 1]])]])

/-- Inspect the actual prepared unfolding of the nested open binder. -/
def fixtureRanks : Option (Nat × Nat × Bool) :=
  match build fixture [] empty with
  | .pending .. => none
  | .done (.mu _ (.node _ [.mk _ [inner]] _ _) _ _) state =>
      match inner with
      | .mu entry body _ _ =>
          match prepare (.interned entry.identity) body with
          | none => none
          | some template => some (headRank inner, headRank (run (compile template inner) state).1, !inner.free.isEmpty)
      | _ => none
  | _ => none

/-- The closed source expression produces an open inner Mu with actual unfolding ranks one and zero. -/
theorem fixture_actual_ranks : fixtureRanks = some (1, 0, true) := by cbv

end MicroCFTA.InternedStoredBodyInvariant
