import MicroCFTA.InternedProfileExecutionFacts

/-!
# Actual recursive requests preserve and use decoded profiles

Complete hits use the invariant for their canonical stored probes. Misses
reserve a fresh name, execute the actual body, and derive the new payload
profile from all three recursive body results. Pending outcomes keep every
complete record verified.
-/
namespace MicroCFTA.InternedProfileRequest
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedRequestFacts
open InternedNestedMissReadback InternedStoredMuOrigins InternedProfileHeap InternedProfileExecutionFacts
open InternedRootProfile InternedProfileEquivalence InternedProfileSemantics InternedFreshProbeKeys
open InternedConstructionProvenance
open InternedBinderProtocol (Reference NodeKey)

/-- The actual hit, miss, and pending branches all preserve the decoded-profile interpretation. -/
theorem request_checked [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (heap : InternedProfileHeap.Heap state)
    (depthSame : Equivalent (profile depth) (normalize .depth (evaluate expression (some [.depth] :: environment.map profile))))
    (ordinarySame : Equivalent (profile ordinary)
      (normalize (.uninterned depth.depth) (evaluate expression (some [.uninterned depth.depth] :: environment.map profile))))
    (recurse : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
      InternedProfileHeap.Heap current → Checked (callback expression environment name current)
        (fun value => Equivalent (profile value) (normalize name (evaluate expression (some [name] :: environment.map profile))))) :
    Checked (request smart depth ordinary (callback expression environment) state)
      (fun value => Equivalent (profile value) (evaluate (.binder smart expression) (environment.map profile))) := by
  have decoded := trans (decode_same .depth (.uninterned depth.depth) depthSame ordinarySame)
    (InternedSyntaxProbeDecoder.source_evaluate_decoded expression (environment.map profile) depth.depth)
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none =>
          simp only [request, installed, present]
          exact pending_checked _ _ _ heap
      | some value =>
          simp only [request, installed, present]
          apply done_checked _ _ _ heap
          have result := hit_profile smart depth ordinary value state normal.facts depthAvailable ordinaryAvailable heap present
          cases smart with
          | false => simpa only [Bool.false_eq_true, ↓reduceIte, evaluate] using result
          | true => exact trans result decoded
  | none =>
      let entry := Cache.intern state.nodes (muKey depth ordinary)
      let allocated := {state with nodes := entry.2}
      have reserved : Normal allocated := reserve_normal (muKey depth ordinary) state normal
      have growth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends state.nodes (muKey depth ordinary) normal.facts.coherent.valid.2
      have allocatedInputs : Values allocated environment :=
        fun value member => (inputs value member).grows state allocated growth history
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (reserve_available (muKey depth ordinary) state normal.facts.coherent normal.facts.cached).2
      have allInputs : Values allocated (.reference (.interned entry.1.identity) :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact argument
        · exact allocatedInputs value member
      have actualChecked := recurse (.interned entry.1.identity) allocated reserved allocatedInputs argument heap
      have actualNormal := callback_normal expression environment (.interned entry.1.identity) allocated reserved allInputs
      have actualVerified := callback_verified expression environment (.interned entry.1.identity) allocated reserved.facts allInputs
      have pending : IsPending (muKey depth ordinary) allocated :=
        ⟨⟨entry.1, (Cache.intern_correct state.nodes _ normal.facts.coherent.valid.2).2.1⟩,
          missing_record state normal.facts.coherent _ installed⟩
      have retained := callback_pending expression environment (.interned entry.1.identity)
        ⟨depth.referenceOf, ordinary.referenceOf⟩ allocated reserved.facts.coherent.valid pending
      simp only [request, installed]
      change Checked ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun value after => complete smart entry.1 value depth ordinary after)) _
      apply bind_checked _ _ _ _ actualChecked
      intro body afterBody returned afterHeap bodySame
      have afterNormal : Normal afterBody := by simpa only [returned, Outcome.state] using actualNormal
      have bodyAvailable := actualVerified.result body afterBody returned
      have candidate := InternedProfileCandidate.candidate expression (environment.map profile) smart entry.1 body depth ordinary
        afterBody afterNormal bodyAvailable (fresh_profiles depth ordinary environment state normal.facts inputs installed)
        depthSame ordinarySame bodySame
      have laterHeap := InternedProfileHeap.complete_heap smart entry.1 body depth ordinary afterBody afterHeap candidate.1
      have absent : afterBody.nodeRecords (muKey depth ordinary) = none := by
        simpa only [returned, Outcome.state, muKey] using retained.2
      have completed : complete smart entry.1 body depth ordinary afterBody =
          .done (finish smart (.mu entry.1 body depth ordinary))
            {afterBody with nodeRecords := keepFirst afterBody.nodeRecords (muKey depth ordinary) (.mu entry.1 body depth ordinary)} := by
        simp [complete, keepFirst, absent, put]
      rw [completed]
      exact done_checked _ _ _ (by simpa only [completed, Outcome.state] using laterHeap) candidate.2

end MicroCFTA.InternedProfileRequest
