import MicroCFTA.InternedBinderFreeProbeCosts
import MicroCFTA.InternedFlatProbeHeap

/-!
# Stored probe costs for complete ordinary and union callbacks

A binder call derives the probe-cost invariant for its newly stored body.
Actual cache hits retain the earlier proof. The result covers both raw and
smart source calls and preserves the invariant on a pending outcome.
-/
namespace MicroCFTA.InternedBinderFreeProbeHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedConstructionProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedLiveEdges InternedNonemptyRecords InternedStoredShallowCompletion
open InternedBinderFreeProbeCosts InternedFreeOccurrenceRank InternedShallowHeap InternedFlatProbeHeap
open InternedBinderProtocol (Reference)

/-- The source root filter allocates no Mu record. -/
theorem filter_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) : NoNewMu state (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact noNewMu_refl state
  case union => split <;> first | exact makeUnion_noNewMu _ state | exact noNewMu_refl state

/-- Complete binder-free normalized source callbacks preserve every earlier Mu payload. -/
theorem normalized_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (free : BinderFree body) :
    NoNewMu state (normalized body captured name state).state :=
  bind_noNewMu state _ _ (build_noNewMu body _ state free)
    (fun value after _ => filter_noNewMu name value after)

/-- An actual raw or smart binder call derives and preserves stored body/probe correspondence. -/
theorem binder_heap [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (live : Live state) (proper : NonemptyRecords state) (inputs : Values state captured)
    (heap : Heap state) (free : BinderFree body) : Heap (build (.binder smart body) captured state).state := by
  obtain ⟨depth, afterDepth, depthDone⟩ := normalized_complete body captured .depth state free
  have depthChecked := normalized_verified body captured .depth state facts (depth_available state) inputs
  have depthFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using depthChecked.facts
  have depthLive : Live afterDepth := by simpa only [depthDone, Outcome.state] using normalized_live body captured .depth state live
  have depthProper : NonemptyRecords afterDepth := by
    simpa only [depthDone, Outcome.state] using normalized_nonempty body captured .depth state proper
  have depthInputs : Values afterDepth captured := fun value member => by
    simpa only [depthDone, Outcome.state] using depthChecked.available value (inputs value member)
  have depthHeap : Heap afterDepth := by
    have kept := preserve state _ heap (normalized_noNewMu body captured .depth state free)
    simpa only [depthDone, Outcome.state] using kept
  obtain ⟨ordinary, afterOrdinary, ordinaryDone⟩ := normalized_complete body captured (.uninterned depth.depth) afterDepth free
  have ordinaryChecked := normalized_verified body captured (.uninterned depth.depth) afterDepth depthFacts
    (ordinary_available afterDepth depth.depth) depthInputs
  have ordinaryFacts : Facts afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.facts
  have ordinaryLive : Live afterOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using normalized_live body captured (.uninterned depth.depth) afterDepth depthLive
  have ordinaryProper : NonemptyRecords afterOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using normalized_nonempty body captured (.uninterned depth.depth) afterDepth depthProper
  have ordinaryInputs : Values afterOrdinary captured := fun value member => by
    simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.available value (depthInputs value member)
  have ordinaryHeap : Heap afterOrdinary := by
    have kept := preserve afterDepth _ depthHeap (normalized_noNewMu body captured (.uninterned depth.depth) afterDepth free)
    simpa only [ordinaryDone, Outcome.state] using kept
  have call : build (.binder smart body) captured state = request smart depth ordinary (normalized body captured) afterOrdinary := by
    rw [build]
    change (normalized body captured .depth state).bind _ = _
    rw [depthDone]
    change (normalized body captured (.uninterned depth.depth) afterDepth).bind _ = _
    rw [ordinaryDone]
    rfl
  rw [call]
  cases installed : afterOrdinary.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases found : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, found, Outcome.state] using ordinaryHeap
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern afterOrdinary.nodes key
      let allocated := {afterOrdinary with nodes := entry.2}
      have allocatedFacts : Facts allocated := reserve_facts key afterOrdinary ordinaryFacts
      have reserved : Available allocated (.reference (.interned entry.1.identity)) :=
        (reserve_available key afterOrdinary ordinaryFacts.coherent ordinaryFacts.cached).2
      have growth : Grows afterOrdinary allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends afterOrdinary.nodes key ordinaryFacts.coherent.valid.2
      have allocatedInputs : Values allocated captured := fun value member =>
        (ordinaryInputs value member).grows afterOrdinary allocated growth history
      obtain ⟨value, final, actualDone⟩ := normalized_complete body captured (.interned entry.1.identity) allocated free
      have finalHeap : Heap final := by
        have kept := preserve allocated _ ordinaryHeap (normalized_noNewMu body captured (.interned entry.1.identity) allocated free)
        simpa only [actualDone, Outcome.state] using kept
      have related : Related (.mu entry.1 value depth ordinary) := by
        intro other count occurrence
        simp only [costs] at occurrence
        obtain ⟨⟨name, prior⟩, selected, equal⟩ := List.mem_map.mp occurrence
        have names : name = other := congrArg Prod.fst equal
        have counts : prior + 1 = count := congrArg Prod.snd equal
        subst name
        have kept := List.mem_filter.mp selected
        refine ⟨prior, counts.symm, ?_⟩
        exact two_probe_cost body captured state allocated facts allocatedFacts live ordinaryLive proper ordinaryProper
          inputs allocatedInputs (.interned entry.1.identity) other reserved (by simpa using kept.2) free
          depth ordinary value afterDepth afterOrdinary final depthDone ordinaryDone actualDone prior kept.1
      simp only [request, installed]
      change Heap ((normalized body captured (.interned entry.1.identity) allocated).bind _).state
      rw [actualDone]
      intro other record stored
      change (keepFirst final.nodeRecords key (.mu entry.1 value depth ordinary)) other = some record at stored
      rcases record_cases final.nodeRecords key other (.mu entry.1 value depth ordinary) record stored with old | ⟨_, same⟩
      · exact finalHeap other record old
      · exact same ▸ related

end MicroCFTA.InternedBinderFreeProbeHeap
