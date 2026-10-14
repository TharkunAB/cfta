import MicroCFTA.InternedPendingScopes
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinaryCoverage

/-!
# Repaired source calls that encounter pending Mu records

Every repaired pending result comes from an actual source callback whose two
normalized probes completed. The witness retains both probe executions,
their complete records, and the exact missing payload at readback.
-/
namespace MicroCFTA.InternedFreshOrdinaryEncounter
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedProbeProvenance InternedFreshProbeKeys InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedPendingScopes InternedPendingOrigins InternedNestedCoverage
open InternedBinderProtocol (Reference NodeKey)

/-- Both normalized probes of the encountered source callback have actually completed before the missing readback. -/
def Encounter [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard) : Prop :=
  ∃ body environment before depth afterDepth ordinary,
    Facts before ∧ Values before environment ∧ Origin key before ∧
    (∃ entry, before.nodes.table key = some entry ∧ .reference (.interned entry.identity) ∈ environment) ∧
    InternedFreshOrdinaryFacts.callback body environment .depth before = .done depth afterDepth ∧
    InternedFreshOrdinaryFacts.callback body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth = .done ordinary final ∧
    Available final depth ∧ Available final ordinary ∧
    key = muKey depth ordinary ∧ IsPending key final

/-- Normalized callback execution derives its record facts on both successful and pending outcomes. -/
theorem callback_verified [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (localAvailable : Available state (.reference name)) :
    Verified state (InternedFreshOrdinaryFacts.callback body environment name state) Available := by
  have all : Values state (.reference name :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact localAvailable
    · exact inputs value member
  exact bind_verified state _ _ Available Available (InternedFreshOrdinaryFacts.build_verified body _ state facts all)
    (fun value after _ afterFacts available => filter_verified name value after afterFacts available)

/-- Earlier lexical inputs remain available after an actual successful source prefix. -/
theorem values_after (verified : Verified before outcome property) (inputs : Values before environment)
    (completed : outcome = .done value after) : Values after environment := by
  intro original member
  simpa only [completed, Outcome.state] using verified.available original (inputs original member)

mutual
/-- Every arbitrary pending source expression has an actual completed pair of encountered callback probes. -/
theorem build_encounter [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : ScopedOrigins waiting environment state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.build expression environment state = .pending key final) : Encounter key final := by
  cases expression with
  | empty | var index => simp [InternedFreshOrdinaryConstruction.build] at pending
  | node edges =>
      cases childrenDone : InternedFreshOrdinaryConstruction.buildEdges edges environment state with
      | pending selected after =>
          simp only [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildEdges_encounter edges environment state facts inputs waiting covered scope _ _ childrenDone
      | done values after => simp [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, work] at pending
  | union members =>
      cases childrenDone : InternedFreshOrdinaryConstruction.buildMany members environment state with
      | pending selected after =>
          simp only [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildMany_encounter members environment state facts inputs waiting covered scope _ _ childrenDone
      | done values after => simp [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, work] at pending
  | binder smart body =>
      have callbackEncounter : ∀ active name current, Facts current → Values current environment →
          Covered active current → ScopedOrigins active (.reference name :: environment) current →
          Available current (.reference name) → ∀ selected after,
          InternedFreshOrdinaryFacts.callback body environment name current = .pending selected after → Encounter selected after := by
        intro active name current currentFacts currentInputs currentCovered currentScope localAvailable selected after stopped
        have all : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact localAvailable
          · exact currentInputs value member
        cases returned : InternedFreshOrdinaryConstruction.build body (.reference name :: environment) current with
        | pending inner finish =>
            simp only [InternedFreshOrdinaryFacts.callback, returned, Outcome.bind, Outcome.pending.injEq] at stopped
            obtain ⟨rfl, rfl⟩ := stopped
            exact build_encounter body _ current currentFacts all active currentCovered currentScope _ _ returned
        | done value finish => simp [InternedFreshOrdinaryFacts.callback, returned, Outcome.bind, work] at stopped
      rw [InternedFreshOrdinaryConstruction.build] at pending
      change ((InternedFreshOrdinaryFacts.callback body environment .depth state).bind fun depth afterDepth =>
        (InternedFreshOrdinaryFacts.callback body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (InternedFreshOrdinaryFacts.callback body environment) afterOrdinary) = .pending key final at pending
      have depthVerified := callback_verified body environment .depth state facts inputs (depth_available state)
      cases depthDone : InternedFreshOrdinaryFacts.callback body environment .depth state with
      | pending selected after =>
          simp only [depthDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact callbackEncounter waiting .depth state facts inputs covered (scope.local _) (depth_available state) _ _ depthDone
      | done depth afterDepth =>
          have depthFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using depthVerified.facts
          have depthInputs := values_after depthVerified inputs depthDone
          have depthCovered := InternedFreshOrdinaryCoverage.callback_covered body environment .depth state facts.coherent.valid covered depth afterDepth depthDone
          have depthGrowth : Grows state afterDepth := by simpa only [depthDone, Outcome.state] using depthVerified.growth
          have depthScope := scope.grows depthGrowth
          have ordinaryVerified := callback_verified body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthFacts depthInputs
            (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
          cases ordinaryDone : InternedFreshOrdinaryFacts.callback body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth with
          | pending selected after =>
              simp only [depthDone, Outcome.bind, ordinaryDone, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact callbackEncounter waiting _ afterDepth depthFacts depthInputs depthCovered (depthScope.local _) (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) _ _ ordinaryDone
          | done ordinary afterOrdinary =>
              have ordinaryFacts : Facts afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.facts
              have ordinaryInputs := values_after ordinaryVerified depthInputs ordinaryDone
              have ordinaryCovered := InternedFreshOrdinaryCoverage.callback_covered body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthFacts.coherent.valid depthCovered ordinary afterOrdinary ordinaryDone
              have ordinaryGrowth : Grows afterDepth afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.growth
              have ordinaryScope := depthScope.grows ordinaryGrowth
              have depthAvailable : Available afterOrdinary depth := by
                simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth (depthVerified.result _ _ depthDone)
              have ordinaryAvailable := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
              simp only [depthDone, Outcome.bind, ordinaryDone] at pending
              cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
              | some entry =>
                  cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) with
                  | some value => simp [request, found, stored] at pending
                  | none =>
                      simp only [request, found, stored, Outcome.pending.injEq] at pending
                      obtain ⟨rfl, rfl⟩ := pending
                      have member : muKey depth ordinary ∈ waiting := by
                        rcases ordinaryCovered.nodes _ entry found with member | ⟨value, impossible⟩
                        · exact member
                        · rw [stored] at impossible; cases impossible
                      exact ⟨body, environment, state, depth, afterDepth, ordinary, facts, inputs,
                        scope.1 _ member, scope.2 _ member, depthDone, ordinaryDone,
                        depthAvailable, ordinaryAvailable, rfl, ⟨entry, found⟩, stored⟩
              | none =>
                  let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
                  let allocated := {afterOrdinary with nodes := entry.2}
                  have allocatedFacts := reserve_facts (muKey depth ordinary) afterOrdinary ordinaryFacts
                  have growth : Grows afterOrdinary allocated :=
                    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
                  have history := intern_issued_extends afterOrdinary.nodes (muKey depth ordinary) ordinaryFacts.coherent.valid.2
                  have allocatedInputs : Values allocated environment := fun value member =>
                    (ordinaryInputs value member).grows afterOrdinary allocated growth history
                  have allocatedCovered := reserve_covered (muKey depth ordinary) afterOrdinary ordinaryCovered
                  have allocatedScope := reserve_scope depth ordinary environment afterOrdinary ordinaryFacts depthAvailable ordinaryAvailable found ordinaryScope
                  have localAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
                    reference_available allocated _ (reserved_reference_issued afterOrdinary.nodes (muKey depth ordinary) ordinaryFacts.coherent.valid.2)
                  simp only [request, found] at pending
                  change (InternedFreshOrdinaryFacts.callback body environment (.interned entry.1.identity) allocated).bind _ = .pending key final at pending
                  cases bodyDone : InternedFreshOrdinaryFacts.callback body environment (.interned entry.1.identity) allocated with
                  | done value after => simp [bodyDone, Outcome.bind] at pending
                  | pending selected after =>
                      simp only [bodyDone, Outcome.bind, Outcome.pending.injEq] at pending
                      obtain ⟨rfl, rfl⟩ := pending
                      exact callbackEncounter (muKey depth ordinary :: waiting) _ allocated allocatedFacts allocatedInputs allocatedCovered allocatedScope localAvailable _ _ bodyDone
termination_by sizeOf expression

/-- A pending child list exposes the first actual stopped source call. -/
theorem buildMany_encounter [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : ScopedOrigins waiting environment state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.buildMany expressions environment state = .pending key final) : Encounter key final := by
  cases expressions with
  | nil => simp [InternedFreshOrdinaryConstruction.buildMany] at pending
  | cons first rest =>
      have firstVerified := InternedFreshOrdinaryFacts.build_verified first environment state facts inputs
      cases firstDone : InternedFreshOrdinaryConstruction.build first environment state with
      | pending selected after =>
          simp only [InternedFreshOrdinaryConstruction.buildMany, firstDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact build_encounter first environment state facts inputs waiting covered scope _ _ firstDone
      | done value after =>
          have afterFacts : Facts after := by simpa only [firstDone, Outcome.state] using firstVerified.facts
          have afterInputs := values_after firstVerified inputs firstDone
          have afterCovered := InternedFreshOrdinaryCoverage.build_covered first environment state facts.coherent.valid covered value after firstDone
          have afterGrowth : Grows state after := by simpa only [firstDone, Outcome.state] using firstVerified.growth
          have afterScope := scope.grows afterGrowth
          cases restDone : InternedFreshOrdinaryConstruction.buildMany rest environment after with
          | done values last => simp [InternedFreshOrdinaryConstruction.buildMany, firstDone, Outcome.bind, restDone] at pending
          | pending selected last =>
              simp only [InternedFreshOrdinaryConstruction.buildMany, firstDone, Outcome.bind, restDone, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact buildMany_encounter rest environment after afterFacts afterInputs waiting afterCovered afterScope _ _ restDone
termination_by sizeOf expressions

/-- A pending edge list comes from an actual nested source child, before ordinary edge interning. -/
theorem buildEdges_encounter [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : ScopedOrigins waiting environment state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.buildEdges expressions environment state = .pending key final) : Encounter key final := by
  cases expressions with
  | nil => simp [InternedFreshOrdinaryConstruction.buildEdges] at pending
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childVerified := InternedFreshOrdinaryFacts.buildMany_verified children environment state facts inputs
          cases childrenDone : InternedFreshOrdinaryConstruction.buildMany children environment state with
          | pending selected after =>
              simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact buildMany_encounter children environment state facts inputs waiting covered scope _ _ childrenDone
          | done values after =>
              have afterFacts : Facts after := by simpa only [childrenDone, Outcome.state] using childVerified.facts
              have afterInputs := values_after childVerified inputs childrenDone
              have afterCovered := InternedFreshOrdinaryCoverage.buildMany_covered children environment state facts.coherent.valid covered values after childrenDone
              have afterGrowth : Grows state after := by simpa only [childrenDone, Outcome.state] using childVerified.growth
              have afterScope := scope.grows afterGrowth
              let edge := run (makeEdge symbol constraint values) after
              have edgeVerified := edge_verified symbol constraint values after afterFacts (childVerified.result _ _ childrenDone)
              have edgeInputs : Values edge.2 environment := values_after edgeVerified afterInputs rfl
              have edgeFacts : Facts edge.2 := edgeVerified.facts
              have edgeCovered := run_covered (makeEdge symbol constraint values) after afterFacts.coherent.valid afterCovered
              have edgeScope := afterScope.grows edgeVerified.growth
              cases restDone : InternedFreshOrdinaryConstruction.buildEdges rest environment edge.2 with
              | done values last =>
                  simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind, work] at pending
                  change (InternedFreshOrdinaryConstruction.buildEdges rest environment edge.2).bind _ = .pending key final at pending
                  simp [restDone, Outcome.bind] at pending
              | pending selected last =>
                  simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind, work] at pending
                  change (InternedFreshOrdinaryConstruction.buildEdges rest environment edge.2).bind _ = .pending key final at pending
                  simp only [restDone, Outcome.bind, Outcome.pending.injEq] at pending
                  obtain ⟨rfl, rfl⟩ := pending
                  exact buildEdges_encounter rest environment edge.2 edgeFacts edgeInputs waiting edgeCovered edgeScope _ _ restDone
termination_by sizeOf expressions
end

/-- Unrestricted closed source execution has a concrete encountered callback and exact completed probe records if it stops pending. -/
theorem closed_encounter [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (state : State Symbol Guard) (pending : InternedFreshOrdinaryConstruction.build expression [] empty = .pending key state) :
    Encounter key state := by
  apply build_encounter expression [] empty empty_facts (by intro value member; cases member) [] empty_correct.2 _ key state pending
  constructor <;> intro key member <;> cases member

end MicroCFTA.InternedFreshOrdinaryEncounter
