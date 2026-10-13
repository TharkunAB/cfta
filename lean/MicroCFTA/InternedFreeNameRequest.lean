import MicroCFTA.InternedFreeNameConstructors

/-!
# Free names through actual recursive source requests

Complete hits use the decoded free names of their stored probes. Misses
reserve a fresh name and use the actual body result. A pending outcome
preserves the free-name invariant of every complete record.
-/
namespace MicroCFTA.InternedFreeNameRequest
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedRequestFacts
open InternedNestedMissReadback InternedStoredMuOrigins InternedFreshProbeKeys
open InternedConstructionProvenance InternedFreeNameDecoder
open InternedBinderProtocol (Reference NodeKey)

/-- A source outcome preserves decoded free names and verifies every returned result. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : InternedFreeNameHeap.Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A returned result preserves the current complete records. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : InternedFreeNameHeap.Heap state) (holds : property value) : Checked (.done value state) property := by
  refine ⟨heap, ?_⟩
  intro result after returned
  cases returned
  exact holds

/-- A pending source lookup returns no unchecked result. -/
theorem pending_checked (key : NodeKey) (state : State Symbol Guard) (property : Result → Prop)
    (heap : InternedFreeNameHeap.Heap state) : Checked (.pending key state) property := by
  refine ⟨heap, ?_⟩
  intro value after impossible
  cases impossible

/-- Source sequencing uses the invariant and result established by the preceding call. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop)
    (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → InternedFreeNameHeap.Heap after → firstProperty value →
      Checked (next value after) property) : Checked (outcome.bind next) property := by
  cases outcome with
  | pending key state => exact pending_checked key state property checked.heap
  | done value state => exact later value state rfl checked.heap (checked.result value state rfl)

/-- The actual callback filter preserves the captured names other than its supplied local. -/
theorem callback_checked [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (captured : List Reference)
    (state : State Symbol Guard) (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (checked : Checked (build expression (.reference name :: environment) state)
      (fun value => ∀ other, other ≠ name → (other ∈ value.free ↔ other ∈ captured))) :
    Checked (callback expression environment name state)
      (fun value => ∀ other, other ≠ name → (other ∈ value.free ↔ other ∈ captured)) := by
  have verified := build_verified expression _ state normal.facts inputs
  have sourceNormal := build_normal expression _ state normal inputs
  unfold callback
  apply bind_checked _ _ _ _ checked
  intro value after returned afterHeap same
  have afterNormal : Normal after := by simpa only [returned, Outcome.state] using sourceNormal
  have available := verified.result value after returned
  apply done_checked
  · exact InternedFreeNameHeap.preserve after _ afterHeap (filter_noNewMu name value after)
  · intro other different
    exact (InternedNormalizationFree.filter_free_other name other value after afterNormal.facts.coherent
      afterNormal.facts.cached afterNormal.facts.linked afterNormal.live available different).trans (same other different)

/-- Actual hit, miss, and pending branches preserve the invariant and recover every captured free name. -/
theorem request_checked [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (captured : List Reference)
    (state : State Symbol Guard) (normal : Normal state) (inputs : Values state environment)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (heap : InternedFreeNameHeap.Heap state) (profileHeap : InternedProfileHeap.Heap state)
    (depthSame : ∀ name, name ≠ .depth → (name ∈ depth.free ↔ name ∈ captured))
    (ordinarySame : ∀ name, name ≠ .uninterned depth.depth → (name ∈ ordinary.free ↔ name ∈ captured))
    (recurse : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
      InternedFreeNameHeap.Heap current → InternedProfileHeap.Heap current →
        Checked (callback expression environment name current)
        (fun value => ∀ other, other ≠ name → (other ∈ value.free ↔ other ∈ captured))) :
    Checked (request smart depth ordinary (callback expression environment) state)
      (fun value => ∀ name, name ∈ value.free ↔ name ∈ captured) := by
  have different : Reference.depth ≠ .uninterned depth.depth := by intro impossible; cases impossible
  have decoded := decode_observed captured depth.free ordinary.free .depth (.uninterned depth.depth)
    different depthSame ordinarySame
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none =>
          simp only [request, installed, present]
          exact pending_checked _ _ _ heap
      | some value =>
          simp only [request, installed, present]
          apply done_checked _ _ _ heap
          intro name
          exact (InternedFreeNameHeap.hit_free smart depth ordinary value state normal.facts depthAvailable
            ordinaryAvailable heap present name).trans (decoded name)
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
      have fresh : .interned entry.1.identity ∉ captured := by
        intro included
        have inDepth := (depthSame (.interned entry.1.identity) (by intro impossible; cases impossible)).mpr included
        change .interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity ∈ depth.free at inDepth
        rw [intern_miss_identity state.nodes _ installed] at inDepth
        exact next_absent state.nodes normal.facts.coherent.valid.2 depth depthAvailable.issued inDepth
      have actualChecked := recurse (.interned entry.1.identity) allocated reserved allocatedInputs argument heap profileHeap
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
      have correct : InternedFreeNameHeap.Correct entry.1 body depth ordinary := by
        intro name
        have candidate := candidate_decoded false entry.1 body depth ordinary captured .depth (.uninterned depth.depth)
          different fresh bodySame depthSame ordinarySame name
        simpa only [finish_free] using candidate
      have laterHeap := InternedFreeNameHeap.complete_heap smart entry.1 body depth ordinary afterBody afterHeap correct
      have absent : afterBody.nodeRecords (muKey depth ordinary) = none := by
        simpa only [returned, Outcome.state, muKey] using retained.2
      have completed : complete smart entry.1 body depth ordinary afterBody =
          .done (finish smart (.mu entry.1 body depth ordinary))
            {afterBody with nodeRecords := keepFirst afterBody.nodeRecords (muKey depth ordinary) (.mu entry.1 body depth ordinary)} := by
        simp [complete, keepFirst, absent, put]
      rw [completed]
      apply done_checked _ _ _ (by simpa only [completed, Outcome.state] using laterHeap)
      intro name
      exact (candidate_decoded smart entry.1 body depth ordinary captured .depth (.uninterned depth.depth)
        different fresh bodySame depthSame ordinarySame name).trans (decoded name)

end MicroCFTA.InternedFreeNameRequest
