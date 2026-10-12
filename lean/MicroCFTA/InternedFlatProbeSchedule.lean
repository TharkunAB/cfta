import MicroCFTA.InternedFlatProbeCosts

/-!
# Free-occurrence costs in the actual two-probe source schedule

The depth probe determines the ordinary placeholder. Both probes run in
source order. Actual reservation supplies the stored body's interned name.
No probe-cost correspondence is assumed at any of these steps.
-/
namespace MicroCFTA.InternedFlatProbeSchedule
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedConstructionProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedFlatProbeCosts InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference)

/-- Every normalized ordinary callback derives full output cache facts. -/
theorem callback_facts [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (facts : Facts state)
    (argument : Available state (.reference name)) (captures : Values state captured) :
    Facts (run (compileBody (template symbol constraint captured) name) state).2 := by
  rw [compileBody_exact symbol constraint captured name state facts argument captures]
  have inputs : Values state (.reference name :: captured) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact captures value member
  let edge := run (makeEdge symbol constraint (.reference name :: captured)) state
  have checked := edge_verified symbol constraint (.reference name :: captured) state facts inputs
  have edgeFacts : Facts edge.2 := checked.facts
  have edgeResident : InternedEdgeResidency.EdgeResident edge.2 edge.1 := checked.result edge.1 edge.2 rfl
  have resident : ∀ selected ∈ [edge.1], InternedEdgeResidency.EdgeResident edge.2 selected := by
    intro selected member
    have same : selected = edge.1 := by simpa using member
    subst selected
    exact edgeResident
  have result := node_verified [edge.1] edge.2 edgeFacts resident
  simpa only [bodyWork, run_bind, work, Outcome.state, edge] using result.facts

/-- Both exact source probes derive coherent complete records and preserve all fixed captures. -/
theorem probes_facts [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (captures : Values state captured) : Facts (probes (template symbol constraint captured) state).2 := by
  let source := template symbol constraint captured
  let first := run (compileBody source .depth) state
  have firstFacts : Facts first.2 := callback_facts symbol constraint captured .depth state facts (depth_available state) captures
  have firstCaptures : Values first.2 captured :=
    fun value member => available_after_run (compileBody source .depth) state facts.coherent.valid (captures value member)
  exact callback_facts symbol constraint captured (.uninterned first.1.depth) first.2 firstFacts
    (ordinary_available first.2 first.1.depth) firstCaptures

/-- The actual source probe pair contains every external occurrence cost of the callback body. -/
theorem source_probes_cost [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state beforeActual : State Symbol Guard)
    (facts : Facts state) (actualFacts : Facts beforeActual) (captures : Values state captured)
    (actualCaptures : Values beforeActual captured) (actual other : Reference) (count : Nat)
    (actualAvailable : Available beforeActual (.reference actual)) (notActual : other ≠ actual)
    (occurrence : (other, count) ∈ costs (run (compileBody (template symbol constraint captured) actual) beforeActual).1) :
    (other, count) ∈ costs (probes (template symbol constraint captured) state).1.1 ∨
      (other, count) ∈ costs (probes (template symbol constraint captured) state).1.2 := by
  let source := template symbol constraint captured
  let first := run (compileBody source .depth) state
  have firstFacts : Facts first.2 := callback_facts symbol constraint captured .depth state facts (depth_available state) captures
  have firstCaptures : Values first.2 captured :=
    fun value member => available_after_run (compileBody source .depth) state facts.coherent.valid (captures value member)
  exact normalized_cost_in_probes symbol constraint captured actual other first.1.depth count beforeActual state first.2
    actualFacts facts firstFacts actualAvailable actualCaptures captures firstCaptures notActual occurrence

/-- Actual source reservation links each fresh stored-body cost to the exact earlier probe records. -/
theorem reserved_body_cost [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (captures : Values state captured) :
    let source := template symbol constraint captured
    let checked := probes source state
    let key := muKey checked.1.1 checked.1.2
    let entry := Cache.intern checked.2.nodes key
    let allocated := {checked.2 with nodes := entry.2}
    ∀ other count, other ≠ .interned entry.1.identity →
      (other, count) ∈ costs (run (compileBody source (.interned entry.1.identity)) allocated).1 →
      (other, count) ∈ costs checked.1.1 ∨ (other, count) ∈ costs checked.1.2 := by
  let source := template symbol constraint captured
  let checked := probes source state
  let key := muKey checked.1.1 checked.1.2
  let entry := Cache.intern checked.2.nodes key
  let allocated := {checked.2 with nodes := entry.2}
  have checkedFacts : Facts checked.2 := probes_facts symbol constraint captured state facts captures
  have afterProbes : Values checked.2 captured := by
    intro value member
    have first := available_after_run (compileBody source .depth) state facts.coherent.valid (captures value member)
    let firstRun := run (compileBody source .depth) state
    exact available_after_run (compileBody source (.uninterned firstRun.1.depth)) firstRun.2
      (run_correct _ _ facts.coherent.valid).1 first
  have allocatedFacts : Facts allocated := reserve_facts key checked.2 checkedFacts
  have reserved := reserve_available key checked.2 checkedFacts.coherent checkedFacts.cached
  have argument : Available allocated (.reference (.interned entry.1.identity)) := reserved.2
  have growth : Grows checked.2 allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := intern_issued_extends checked.2.nodes key checkedFacts.coherent.valid.2
  have allocatedCaptures : Values allocated captured :=
    fun value member => (afterProbes value member).grows checked.2 allocated growth history
  dsimp only
  intro other count different occurrence
  exact source_probes_cost symbol constraint captured state allocated facts allocatedFacts captures allocatedCaptures
    (.interned entry.1.identity) other count argument different occurrence

/-- A fresh completed raw Mu stores the actual body whose external costs occur in its canonical probes. -/
theorem fresh_mu_cost [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (captures : Values state captured)
    (missing : (probes (template symbol constraint captured) state).2.nodeRecords
      (muKey (probes (template symbol constraint captured) state).1.1 (probes (template symbol constraint captured) state).1.2) = none)
    (other : Reference) (count : Nat)
    (occurrence : (other, count) ∈ costs (internMu (template symbol constraint captured) state).1) :
    ∃ prior, count = prior + 1 ∧
      ((other, prior) ∈ costs (probes (template symbol constraint captured) state).1.1 ∨
       (other, prior) ∈ costs (probes (template symbol constraint captured) state).1.2) := by
  let source := template symbol constraint captured
  let checked := probes source state
  have actual := finishMu_miss source checked.1.1 checked.1.2 checked.2 missing
  change (other, count) ∈ costs (finishMu source checked.1.1 checked.1.2 checked.2).1 at occurrence
  rw [actual] at occurrence
  simp only [costs] at occurrence
  obtain ⟨⟨name, prior⟩, selected, equal⟩ := List.mem_map.mp occurrence
  have names : name = other := congrArg Prod.fst equal
  have counts : prior + 1 = count := congrArg Prod.snd equal
  subst name
  have kept := List.mem_filter.mp selected
  exact ⟨prior, counts.symm, reserved_body_cost symbol constraint captured state facts captures other prior
    (by simpa using kept.2) kept.1⟩

end MicroCFTA.InternedFlatProbeSchedule
