import MicroCFTA.InternedFreshOrdinaryCostExecutionFacts

/-!
# Cost readback through the repaired recursive request schedule

A hit uses the stored weighted observation. A miss retains both probes,
reserves a fresh actual name, and checks its callback before completion.
The existing depth theorem supplies the final smart retention decision.
Recursive callback cost observations remain explicit for the syntax induction.
-/
namespace MicroCFTA.InternedFreshOrdinaryCostRequest
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish IsPending)
open InternedNestedRequestFacts InternedConstructionProvenance InternedFreshProbeKeys
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryPending InternedFreeOccurrenceRank
open InternedFreshOrdinaryCostHeap InternedFreshOrdinaryCostExecutionFacts
open InternedBinderProtocol (Reference NodeKey)

/-- Every actual request preserves weighted records and returns the exact decoded cost list. -/
theorem request_checked [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (captured : List (Reference × Nat))
    (depthSame : ∀ name count, name ≠ .depth → ((name, count) ∈ costs depth ↔ (name, count) ∈ captured))
    (ordinarySame : ∀ name count, name ≠ .uninterned (ordinaryLevel depth) →
      ((name, count) ∈ costs ordinary ↔ (name, count) ∈ captured))
    (finalDepthHeap : InternedFreshOrdinaryDepthHeap.Heap
      (request smart depth ordinary (callback expression environment) state).state)
    (recurse : ∀ name current, Context current environment → Available current (.reference name) →
      Heap current → InternedFreshOrdinaryDepthHeap.Heap current →
      Checked (callback expression environment name current)
        (fun value => ∀ other count, other ≠ name → ((other, count) ∈ costs value ↔ (other, count) ∈ captured))) :
    Checked (request smart depth ordinary (callback expression environment) state)
      (fun value => Agrees value (decodedCosts smart depth ordinary)) := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none =>
          simp only [request, installed, present]
          exact pending_checked _ _ _ heap
      | some value =>
          simp only [request, installed, present]
          exact done_checked _ _ _ heap
            (hit_agrees smart depth ordinary value state context.normal.facts depthAvailable ordinaryAvailable heap depthHeap present)
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have reserved : Context allocated environment := context.reserve key
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (reserve_available key state context.normal.facts.coherent context.normal.facts.cached).2
      have fresh : .interned entry.1.identity ∉ depth.free := by
        intro member
        change .interned (Cache.intern state.nodes key).1.identity ∈ depth.free at member
        rw [intern_miss_identity state.nodes key installed] at member
        exact next_absent state.nodes context.normal.facts.coherent.valid.2 depth depthAvailable.issued member
      have pending : IsPending key allocated :=
        ⟨⟨entry.1, (Cache.intern_correct state.nodes key context.normal.facts.coherent.valid.2).2.1⟩,
          InternedNestedMissReadback.missing_record state context.normal.facts.coherent key installed⟩
      have retained := callback_pending expression environment (.interned entry.1.identity)
        ⟨depth.referenceOf, ordinary.referenceOf⟩ allocated reserved.normal.facts.coherent.valid pending
      have actual := recurse (.interned entry.1.identity) allocated reserved argument heap depthHeap
      simp only [request, installed]
      change Checked ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun body after => complete smart entry.1 body depth ordinary after)) _
      apply bind_checked _ _ _ _ actual
      intro body afterBody returned afterHeap bodyCorrect
      have absent : afterBody.nodeRecords key = none := by
        simpa only [returned, Outcome.state, key, muKey] using retained.2
      let final := {afterBody with nodeRecords := keepFirst afterBody.nodeRecords key (.mu entry.1 body depth ordinary)}
      have completed : complete smart entry.1 body depth ordinary afterBody =
          .done (finish smart (.mu entry.1 body depth ordinary)) final := by
        simp [complete, final, key, keepFirst, absent, put]
      have whole : request smart depth ordinary (callback expression environment) state =
          .done (finish smart (.mu entry.1 body depth ordinary)) final := by
        simp only [request, installed]
        change (callback expression environment (.interned entry.1.identity) allocated).bind
          (fun body after => complete smart entry.1 body depth ordinary after) = _
        rw [returned]
        exact completed
      have decodedHeap : InternedFreshOrdinaryDepthHeap.Heap final := by
        simpa only [whole, Outcome.state] using finalDepthHeap
      have present : final.nodeRecords key = some (.mu entry.1 body depth ordinary) := by
        simp [final, keepFirst, absent, put]
      have bodyInputs := (reserved.local _ argument).inputs
      have verified := callback_verified expression environment (.interned entry.1.identity) allocated reserved.normal.facts bodyInputs
      have afterContext : Context afterBody environment := by
        simpa only [returned, Outcome.state] using reserved.callback expression (.interned entry.1.identity) argument
      have correct := candidate entry.1 body depth ordinary state context.normal.facts.coherent depthAvailable captured
        (InternedDeepLocalNormal.callback_local expression environment (.interned entry.1.identity) allocated
          reserved.normal bodyInputs body afterBody returned) fresh depthSame ordinarySame bodyCorrect
      have finalHeap := complete_heap smart entry.1 body depth ordinary afterBody afterHeap correct
      rw [completed]
      exact done_checked _ _ _ (by simpa only [completed, Outcome.state] using finalHeap)
        (finish_agrees smart entry.1 body depth ordinary afterBody afterContext.normal.facts.coherent
          (verified.result body afterBody returned) correct (decodedHeap key entry.1 body depth ordinary present))

end MicroCFTA.InternedFreshOrdinaryCostRequest
