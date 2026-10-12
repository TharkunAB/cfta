import MicroCFTA.InternedFreeOccurrenceNode
import MicroCFTA.InternedShallowValues

/-!
# Actual body and probe costs for an ordinary constructor callback

The callback puts its supplied reference before fixed captured records in
one ordinary edge. Source edge removal depends only on those fixed
records. For another name, every occurrence cost therefore agrees across
the actual body and any probe whose supplied name is different.
-/
namespace MicroCFTA.InternedFlatProbeCosts
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedFreeOccurrenceRank InternedFreeOccurrenceNode InternedShallowValues
open InternedBinderProtocol (Reference)

/-- An ordinary source callback retains the supplied recursive reference and its fixed captures. -/
def bodyWork (symbol : Symbol) (constraint : Guard) (captured : List (Value Symbol Guard))
    (name : Reference) : Work Symbol Guard (Value Symbol Guard) :=
  (makeEdge symbol constraint (.reference name :: captured)).bind fun edge => makeNode [edge]

/-- The callback is an existing finite constructor template with the exact ordered captures. -/
def template (symbol : Symbol) (constraint : Guard) (captured : List (Value Symbol Guard)) : Template Symbol Guard :=
  .node [.mk symbol constraint (.argument :: captured.map Template.captured)]

/-- Compiling fixed captured records does not allocate or change their payloads. -/
theorem compile_captures (captured : List (Value Symbol Guard)) (argument : Value Symbol Guard) :
    compileMany (captured.map Template.captured) argument = .pure captured := by
  induction captured with
  | nil => simp [compileMany]
  | cons first rest ih => simp [compileMany, compile, Work.bind, ih]

/-- The adapter executes exactly the existing source template compiler. -/
theorem compile_template (symbol : Symbol) (constraint : Guard) (captured : List (Value Symbol Guard)) (name : Reference) :
    compile (template symbol constraint captured) (.reference name) = bodyWork symbol constraint captured name := by
  simp [template, bodyWork, compile, compileEdges, compileMany, compile_captures, Work.bind, makeEdge]

/-- Ordinary source construction cannot expose a root union to self-reference filtering. -/
theorem makeNode_filter [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : InternedEdgeResidency.Linked state)
    (resident : ∀ edge ∈ edges, InternedEdgeResidency.EdgeResident state edge) :
    withoutSelfReference name (run (makeNode edges) state).1 = .pure (run (makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), InternedEdgeResidency.EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · simp [run, withoutSelfReference]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, readback, identifyNode, withoutSelfReference]

/-- Both source probes and the stored body include the current root self-filter.
For this ordinary callback the filter retains the exact result and cache state. -/
theorem compileBody_exact [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (facts : Facts state)
    (argument : Available state (.reference name)) (captures : Values state captured) :
    run (compileBody (template symbol constraint captured) name) state = run (bodyWork symbol constraint captured name) state := by
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
  rw [compileBody, compile_template, run_bind]
  simp only [bodyWork, run_bind]
  change run (withoutSelfReference name (run (makeNode [edge.1]) edge.2).1) (run (makeNode [edge.1]) edge.2).2 = _
  rw [makeNode_filter name [edge.1] edge.2 edgeFacts.coherent edgeFacts.linked resident]
  rfl

/-- The source edge survives precisely when each fixed captured record is nonempty. -/
def CapturedLive (captured : List (Value Symbol Guard)) : Prop :=
  ∀ value ∈ captured, value.referenceOf ≠ .empty

/-- The exact occurrence profile follows actual edge allocation, empty-child removal,
canonical node construction, and complete cache readback. -/
theorem body_cost_iff [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (facts : Facts state)
    (argument : Available state (.reference name)) (captures : Values state captured)
    (other : Reference) (count : Nat) :
    (other, count) ∈ costs (run (bodyWork symbol constraint captured name) state).1 ↔
      CapturedLive captured ∧ ((other = name ∧ count = 0) ∨ ∃ value ∈ captured, (other, count) ∈ costs value) := by
  have inputs : Values state (.reference name :: captured) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact captures value member
  let edge := run (makeEdge symbol constraint (.reference name :: captured)) state
  have checked := edge_verified symbol constraint (.reference name :: captured) state facts inputs
  have edgeFacts : Facts edge.2 := checked.facts
  have edgeResident : InternedEdgeResidency.EdgeResident edge.2 edge.1 := checked.result edge.1 edge.2 rfl
  have children : edge.1.children = .reference name :: captured :=
    makeEdge_children symbol constraint _ state facts.coherent facts.cached inputs
  rw [bodyWork, run_bind]
  change (other, count) ∈ costs (run (makeNode [edge.1]) edge.2).1 ↔ _
  have resident : ∀ selected ∈ [edge.1], InternedEdgeResidency.EdgeResident edge.2 selected := by
    intro selected member
    have same : selected = edge.1 := by simpa using member
    subst selected
    exact edgeResident
  rw [makeNode_cost_iff [edge.1] edge.2 edgeFacts.coherent edgeFacts.linked resident]
  simp only [List.mem_singleton, exists_eq_left, children]
  have live : ((Value.reference name :: captured).any (fun child => child.referenceOf == .empty) = false) ↔
      CapturedLive captured := by
    simp [CapturedLive, List.any_eq_false, Value.referenceOf]
  rw [live]
  simp [costs]

/-- A probe with a different supplied name has exactly the fixed captured occurrence costs. -/
theorem body_cost_other [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) (facts : Facts state)
    (argument : Available state (.reference name)) (captures : Values state captured)
    (other : Reference) (different : other ≠ name) (count : Nat) :
    (other, count) ∈ costs (run (bodyWork symbol constraint captured name) state).1 ↔
      CapturedLive captured ∧ ∃ value ∈ captured, (other, count) ∈ costs value := by
  simpa [different] using body_cost_iff symbol constraint captured name state facts argument captures other count

/-- The actual body and a noncapturing probe agree at each external name and cost. -/
theorem body_probe_cost [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (actual probe other : Reference) (count : Nat)
    (beforeActual beforeProbe : State Symbol Guard) (actualFacts : Facts beforeActual) (probeFacts : Facts beforeProbe)
    (actualAvailable : Available beforeActual (.reference actual)) (probeAvailable : Available beforeProbe (.reference probe))
    (actualCaptures : Values beforeActual captured) (probeCaptures : Values beforeProbe captured)
    (notActual : other ≠ actual) (notProbe : other ≠ probe) :
    (other, count) ∈ costs (run (bodyWork symbol constraint captured actual) beforeActual).1 ↔
      (other, count) ∈ costs (run (bodyWork symbol constraint captured probe) beforeProbe).1 :=
  (body_cost_other symbol constraint captured actual beforeActual actualFacts actualAvailable actualCaptures other notActual count).trans
    (body_cost_other symbol constraint captured probe beforeProbe probeFacts probeAvailable probeCaptures other notProbe count).symm

/-- At least one of the two distinct source placeholder names preserves every external body cost.
The result follows from the callback operations, not an assumed probe equation. -/
theorem body_cost_in_probes [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (actual other : Reference) (level count : Nat)
    (beforeActual beforeDepth beforeOrdinary : State Symbol Guard)
    (actualFacts : Facts beforeActual) (depthFacts : Facts beforeDepth) (ordinaryFacts : Facts beforeOrdinary)
    (actualAvailable : Available beforeActual (.reference actual))
    (actualCaptures : Values beforeActual captured) (depthCaptures : Values beforeDepth captured)
    (ordinaryCaptures : Values beforeOrdinary captured) (notActual : other ≠ actual)
    (occurrence : (other, count) ∈ costs (run (bodyWork symbol constraint captured actual) beforeActual).1) :
    (other, count) ∈ costs (run (bodyWork symbol constraint captured .depth) beforeDepth).1 ∨
      (other, count) ∈ costs (run (bodyWork symbol constraint captured (.uninterned level)) beforeOrdinary).1 := by
  by_cases selected : other = .depth
  · right
    apply (body_probe_cost symbol constraint captured actual (.uninterned level) other count beforeActual beforeOrdinary
      actualFacts ordinaryFacts actualAvailable (ordinary_available beforeOrdinary level) actualCaptures ordinaryCaptures notActual
      (by simp [selected])).mp occurrence
  · left
    apply (body_probe_cost symbol constraint captured actual .depth other count beforeActual beforeDepth
      actualFacts depthFacts actualAvailable (depth_available beforeDepth) actualCaptures depthCaptures notActual selected).mp occurrence

/-- The exact existing normalized source callback preserves each external occurrence in one of its two probes. -/
theorem normalized_cost_in_probes [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (captured : List (Value Symbol Guard)) (actual other : Reference) (level count : Nat)
    (beforeActual beforeDepth beforeOrdinary : State Symbol Guard)
    (actualFacts : Facts beforeActual) (depthFacts : Facts beforeDepth) (ordinaryFacts : Facts beforeOrdinary)
    (actualAvailable : Available beforeActual (.reference actual))
    (actualCaptures : Values beforeActual captured) (depthCaptures : Values beforeDepth captured)
    (ordinaryCaptures : Values beforeOrdinary captured) (notActual : other ≠ actual)
    (occurrence : (other, count) ∈ costs (run (compileBody (template symbol constraint captured) actual) beforeActual).1) :
    (other, count) ∈ costs (run (compileBody (template symbol constraint captured) .depth) beforeDepth).1 ∨
      (other, count) ∈ costs (run (compileBody (template symbol constraint captured) (.uninterned level)) beforeOrdinary).1 := by
  rw [compileBody_exact symbol constraint captured actual beforeActual actualFacts actualAvailable actualCaptures] at occurrence
  rw [compileBody_exact symbol constraint captured .depth beforeDepth depthFacts (depth_available beforeDepth) depthCaptures,
    compileBody_exact symbol constraint captured (.uninterned level) beforeOrdinary ordinaryFacts (ordinary_available beforeOrdinary level) ordinaryCaptures]
  exact body_cost_in_probes symbol constraint captured actual other level count beforeActual beforeDepth beforeOrdinary
    actualFacts depthFacts ordinaryFacts actualAvailable actualCaptures depthCaptures ordinaryCaptures notActual occurrence

end MicroCFTA.InternedFlatProbeCosts
