import MicroCFTA.InternedBinderFreeObservations

/-!
# Actual normalized callback costs through ordinary and union syntax

The callback runs the complete source executor and then removes root self
operands. Every external occurrence has the same cost in a probe with a
different supplied reference. Two distinct source placeholders cover every
external body occurrence, including placeholder names in captured values.
-/
namespace MicroCFTA.InternedBinderFreeProbeCosts
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedLiveEdges InternedNonemptyRecords InternedStoredShallowCompletion
open InternedOccurrenceObservations InternedBinderFreeObservations
open InternedFreeOccurrenceRank InternedFreeOccurrenceNormalization InternedFreeOccurrenceExact
open InternedBinderProtocol (Reference)

/-- Source root self filtering removes no occurrence of a different name and adds no cost. -/
theorem filter_cost_iff [DecidableEq (EdgeKey Symbol Guard)] (name other : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (live : Live state) (available : Available state value) (different : other ≠ name) (count : Nat) :
    (other, count) ∈ costs (run (withoutSelfReference name value) state).1 ↔ (other, count) ∈ costs value := by
  constructor
  · intro present
    cases value <;> simp only [withoutSelfReference, run] at present <;> try exact present
    case union entry members depth free =>
      split at present
      · obtain ⟨source, member, occurrence⟩ := makeUnion_cost_origin _ state facts.coherent facts.cached facts.linked
          (fun value included => available.children value (List.mem_filter.mp included).1) (other, count) present
        simpa only [costs] using (many_member members (other, count)).mpr
          ⟨source, (List.mem_filter.mp member).1, occurrence⟩
      · exact present
  · exact filter_cost_other name other value state facts.coherent facts.cached facts.linked live available different count

/-- The callback is exactly the normalized callback used by the nested source constructor. -/
def normalized [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) :
    Outcome Symbol Guard (Value Symbol Guard) :=
  (build body (.reference name :: captured) state).bind fun value after => work (withoutSelfReference name value) after

/-- Every binder-free callback completes after the actual source root filter. -/
theorem normalized_complete [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (free : BinderFree body) :
    ∃ value final, normalized body captured name state = .done value final := by
  obtain ⟨value, after, completed⟩ := build_complete body (.reference name :: captured) state free
  exact ⟨(run (withoutSelfReference name value) after).1, (run (withoutSelfReference name value) after).2, by simp only [normalized, completed, Outcome.bind, work]⟩

/-- Normalized callback execution derives all source cache and availability facts. -/
theorem normalized_verified [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (facts : Facts state) (argument : Available state (.reference name)) (inputs : Values state captured) :
    Verified state (normalized body captured name state) Available := by
  have values : Values state (.reference name :: captured) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact inputs value member
  exact bind_verified _ _ _ _ _ (build_verified body _ state facts values)
    (fun value after _ later present => filter_verified name value after later present)

/-- Arbitrary nested callback syntax preserves stored live-edge normalization. -/
theorem normalized_live [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (live : Live state) :
    Live (normalized body captured name state).state :=
  bind_live _ _ (build_live body _ state live) (fun value after _ later => filter_live name value after later)

/-- Arbitrary nested callback syntax preserves actual stored constructor shapes. -/
theorem normalized_nonempty [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (proper : NonemptyRecords state) :
    NonemptyRecords (normalized body captured name state).state :=
  bind_nonempty _ _ (build_nonempty body _ state proper) (fun value after _ later => filter_nonempty name value after later)

/-- Fixed captures agree at every position, with no restriction on their Mu depth. -/
theorem captures_same (name : Reference) (values : List (Value Symbol Guard)) : Paired (Same name) values values := by
  induction values with
  | nil => exact .nil
  | cons first rest ih => exact .cons (same_refl name first) ih

/-- The two complete normalized outputs have identical occurrence costs for an external name. -/
theorem normalized_costs [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (first second other : Reference) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left captured) (ri : Values right captured)
    (la : Available left (.reference first)) (ra : Available right (.reference second))
    (notFirst : other ≠ first) (notSecond : other ≠ second) (free : BinderFree body)
    (a b : Value Symbol Guard) (afterA afterB : State Symbol Guard)
    (ea : normalized body captured first left = .done a afterA)
    (eb : normalized body captured second right = .done b afterB) :
    ∀ count, (other, count) ∈ costs a ↔ (other, count) ∈ costs b := by
  have ia : Values left (.reference first :: captured) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact la
    · exact li value member
  have ib : Values right (.reference second :: captured) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ra
    · exact ri value member
  obtain ⟨rawA, nextA, rawB, nextB, ba, bb, related⟩ :=
    build_same other body _ _ left right lf rf ll rl ln rn ia ib
      (.cons (reference_same other first second notFirst notSecond) (captures_same other captured)) free
  have ca := build_verified body _ left lf ia
  have cb := build_verified body _ right rf ib
  have fa : Facts nextA := by simpa only [ba, Outcome.state] using ca.facts
  have fb : Facts nextB := by simpa only [bb, Outcome.state] using cb.facts
  have liveA : Live nextA := by simpa only [ba, Outcome.state] using build_live body (.reference first :: captured) left ll
  have liveB : Live nextB := by simpa only [bb, Outcome.state] using build_live body (.reference second :: captured) right rl
  simp only [normalized, ba, Outcome.bind, work, Outcome.done.injEq] at ea
  simp only [normalized, bb, Outcome.bind, work, Outcome.done.injEq] at eb
  intro count
  rw [← ea.1, ← eb.1,
    filter_cost_iff first other rawA nextA fa liveA (ca.result rawA nextA ba) notFirst count,
    filter_cost_iff second other rawB nextB fb liveB (cb.result rawB nextB bb) notSecond count]
  exact related.2 count

/-- The actual ordered source probes contain every external occurrence of a complete actual body. -/
theorem two_probe_cost [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (captured : List (Value Symbol Guard)) (state actualState : State Symbol Guard)
    (facts : Facts state) (actualFacts : Facts actualState) (live : Live state) (actualLive : Live actualState)
    (proper : NonemptyRecords state) (actualProper : NonemptyRecords actualState)
    (inputs : Values state captured) (actualInputs : Values actualState captured)
    (actual other : Reference) (actualAvailable : Available actualState (.reference actual))
    (different : other ≠ actual) (free : BinderFree body)
    (depth ordinary value : Value Symbol Guard) (afterDepth afterOrdinary afterActual : State Symbol Guard)
    (depthDone : normalized body captured .depth state = .done depth afterDepth)
    (ordinaryDone : normalized body captured (.uninterned depth.depth) afterDepth = .done ordinary afterOrdinary)
    (actualDone : normalized body captured actual actualState = .done value afterActual)
    (count : Nat) (occurrence : (other, count) ∈ costs value) :
    (other, count) ∈ costs depth ∨ (other, count) ∈ costs ordinary := by
  by_cases depthName : other = .depth
  · right
    have checked := normalized_verified body captured .depth state facts (depth_available state) inputs
    have nextFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using checked.facts
    have nextLive : Live afterDepth := by simpa only [depthDone, Outcome.state] using normalized_live body captured .depth state live
    have nextProper : NonemptyRecords afterDepth := by
      simpa only [depthDone, Outcome.state] using normalized_nonempty body captured .depth state proper
    have nextInputs : Values afterDepth captured := fun value member => by
      simpa only [depthDone, Outcome.state] using checked.available value (inputs value member)
    exact (normalized_costs body captured actual (.uninterned depth.depth) other actualState afterDepth
      actualFacts nextFacts actualLive nextLive actualProper nextProper actualInputs nextInputs actualAvailable
      (ordinary_available afterDepth depth.depth) different (by simp [depthName]) free value ordinary afterActual afterOrdinary
      actualDone ordinaryDone count).mp occurrence
  · left
    exact (normalized_costs body captured actual .depth other actualState state
      actualFacts facts actualLive live actualProper proper actualInputs inputs actualAvailable
      (depth_available state) different depthName free value depth afterActual afterDepth actualDone depthDone count).mp occurrence

end MicroCFTA.InternedBinderFreeProbeCosts
