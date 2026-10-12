import MicroCFTA.InternedFlatProbeSchedule

/-!
# Stored body/probe costs through source cache hits

Every newly completed binder in the ordinary callback fragment derives its
body/probe cost relation. Earlier complete records retain that relation.
A canonical cache hit therefore returns a record with the proved relation,
without assuming that the cache hit re-executes its callback.
-/
namespace MicroCFTA.InternedFlatProbeHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedConstructionProvenance
open InternedNestedFacts InternedNestedProvenance
open InternedFlatProbeCosts InternedFlatProbeSchedule InternedFreeOccurrenceRank InternedShallowHeap
open InternedBinderProtocol (Reference NodeKey)

/-- Each completed Mu occurrence has its predecessor cost in an actual canonical probe. -/
def Related : Value Symbol Guard → Prop
  | value@(.mu _ _ depth ordinary) => ∀ name count, (name, count) ∈ costs value →
      ∃ prior, count = prior + 1 ∧ ((name, prior) ∈ costs depth ∨ (name, prior) ∈ costs ordinary)
  | _ => True

/-- Every actual complete Mu payload carries the derived body/probe relation. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value → Related value

theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value stored
  cases stored

/-- Ordinary effects preserve the relation when they introduce no Mu payload. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before) (ordinary : NoNewMu before after) : Heap after := by
  intro key value stored
  cases value with
  | empty | reference | node | union => trivial
  | mu entry body depth shape => exact heap key _ (ordinary key entry body depth shape stored)

/-- The actual normalized ordinary callback cannot replace or add a completed Mu payload. -/
theorem callback_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (facts : Facts state)
    (argument : Available state (.reference name)) (captures : Values state captured) :
    NoNewMu state (run (compileBody (template symbol constraint captured) name) state).2 := by
  rw [compileBody_exact symbol constraint captured name state facts argument captures, bodyWork, run_bind]
  let edge := run (makeEdge symbol constraint (.reference name :: captured)) state
  have first : NoNewMu state edge.2 := by intro key entry body depth shape stored; exact stored
  exact noNewMu_trans first (makeNode_noNewMu [edge.1] edge.2)

/-- Both actual source probes preserve every earlier Mu payload's proved relation. -/
theorem probes_heap [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (captures : Values state captured) (heap : Heap state) : Heap (probes (template symbol constraint captured) state).2 := by
  let source := template symbol constraint captured
  let first := run (compileBody source .depth) state
  have firstFacts : Facts first.2 := callback_facts symbol constraint captured .depth state facts (depth_available state) captures
  have firstCaptures : Values first.2 captured :=
    fun value member => available_after_run (compileBody source .depth) state facts.coherent.valid (captures value member)
  have firstHeap := preserve state first.2 heap (callback_noNewMu symbol constraint captured .depth state facts (depth_available state) captures)
  exact preserve first.2 _ firstHeap (callback_noNewMu symbol constraint captured (.uninterned first.1.depth)
    first.2 firstFacts (ordinary_available first.2 first.1.depth) firstCaptures)

/-- The actual source constructor preserves the stored relation on both fresh completion and canonical hits. -/
theorem internMu_properties [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (captures : Values state captured) (heap : Heap state) : Heap (internMu (template symbol constraint captured) state).2 ∧
      InternedEdgeResidency.Linked (internMu (template symbol constraint captured) state).2 := by
  let source := template symbol constraint captured
  let checked := probes source state
  let key := muKey checked.1.1 checked.1.2
  have checkedFacts : Facts checked.2 := probes_facts symbol constraint captured state facts captures
  have checkedHeap : Heap checked.2 := probes_heap symbol constraint captured state facts captures heap
  cases found : checked.2.nodeRecords key with
  | some value => simpa only [internMu, finishMu, source, checked, key, found] using And.intro checkedHeap checkedFacts.linked
  | none =>
      let entry := Cache.intern checked.2.nodes key
      let allocated := {checked.2 with nodes := entry.2}
      let body := run (compileBody source (.interned entry.1.identity)) allocated
      let candidate := Value.mu entry.1 body.1 checked.1.1 checked.1.2
      have allocatedFacts : Facts allocated := reserve_facts key checked.2 checkedFacts
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (reserve_available key checked.2 checkedFacts.coherent checkedFacts.cached).2
      have checkedCaptures : Values checked.2 captured := by
        intro value member
        let first := run (compileBody source .depth) state
        exact available_after_run (compileBody source (.uninterned first.1.depth)) first.2
          (run_correct _ _ facts.coherent.valid).1
          (available_after_run (compileBody source .depth) state facts.coherent.valid (captures value member))
      have growth : Grows checked.2 allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends checked.2.nodes key checkedFacts.coherent.valid.2
      have allocatedCaptures : Values allocated captured :=
        fun value member => (checkedCaptures value member).grows checked.2 allocated growth history
      have allocatedHeap : Heap allocated := checkedHeap
      have bodyHeap : Heap body.2 := preserve allocated body.2 allocatedHeap
        (callback_noNewMu symbol constraint captured (.interned entry.1.identity) allocated allocatedFacts argument allocatedCaptures)
      have bodyFacts : Facts body.2 := callback_facts symbol constraint captured (.interned entry.1.identity)
        allocated allocatedFacts argument allocatedCaptures
      have related : Related candidate := by
        intro name count occurrence
        simp only [costs] at occurrence
        obtain ⟨⟨other, prior⟩, selected, equal⟩ := List.mem_map.mp occurrence
        have names : other = name := congrArg Prod.fst equal
        have counts : prior + 1 = count := congrArg Prod.snd equal
        subst other
        have kept := List.mem_filter.mp selected
        exact ⟨prior, counts.symm, reserved_body_cost symbol constraint captured state facts captures name prior
          (by simpa using kept.2) kept.1⟩
      change checked.2.nodeRecords (muKey checked.1.1 checked.1.2) = none at found
      constructor
      · intro other value stored
        change (finishMu source checked.1.1 checked.1.2 checked.2).2.nodeRecords other = some value at stored
        simp only [finishMu, found] at stored
        change (keepFirst body.2.nodeRecords key candidate) other = some value at stored
        rcases record_cases body.2.nodeRecords key other candidate value stored with old | ⟨_, same⟩
        · exact bodyHeap other value old
        · exact same ▸ related
      · intro other value stored edge member
        change (finishMu source checked.1.1 checked.1.2 checked.2).2.nodeRecords other = some value at stored
        simp only [finishMu, found] at stored
        change (keepFirst body.2.nodeRecords key candidate) other = some value at stored
        rcases record_cases body.2.nodeRecords key other candidate value stored with old | ⟨_, same⟩
        · have retained := bodyFacts.linked other value old edge member
          change (finishMu source checked.1.1 checked.1.2 checked.2).2.edgeRecords edge.entry.key = some edge
          simpa only [finishMu, found, InternedEdgeResidency.EdgeResident, body, allocated, entry, key] using retained
        · subst value
          simp [candidate, InternedEdgeResidency.nodeEdges] at member

/-- The actual source constructor preserves the derived relation for every stored record. -/
theorem internMu_heap [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (captures : Values state captured) (heap : Heap state) : Heap (internMu (template symbol constraint captured) state).2 :=
  (internMu_properties symbol constraint captured state facts captures heap).1

/-- Both constructor result paths read a record with the proved source body/probe relation. -/
theorem internMu_related [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (captures : Values state captured) (heap : Heap state) : Related (internMu (template symbol constraint captured) state).1 := by
  let source := template symbol constraint captured
  let checked := probes source state
  exact internMu_heap symbol constraint captured state facts captures heap (muKey checked.1.1 checked.1.2)
    _ (finishMu_stored source checked.1.1 checked.1.2 checked.2)

end MicroCFTA.InternedFlatProbeHeap
