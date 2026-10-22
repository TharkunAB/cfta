import MicroCFTA.MergedColdReaderTermination
import MicroCFTA.InternedShallowValues

/-!
# Closed inputs through binder-free physical construction

The edge reader rebuilds prepared Mu bodies without new binder requests.
Closed lexical inputs therefore produce a closed result. The proof uses
actual constructor readback and needs no free-name semantic heap.
-/
namespace MicroCFTA.MergedColdReaderClosedInputs
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open InternedEdgeResidency InternedNormalizationFree InternedShallowValues
open InternedStoredShallowCompletion

/-- Every source value in a list has no cached free reference. -/
def ClosedValues (values : List (Value Symbol Guard)) : Prop := ∀ value ∈ values, value.free = []

/-- Every stored child in an edge list has no cached free reference. -/
def ClosedEdges (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, ClosedValues edge.children

/-- Ordinary physical construction preserves closed retained children. -/
theorem makeNode_closed [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : Edges state edges) (closed : ClosedEdges edges) :
    (run (makeNode edges) state).1.free = [] := by
  rw [makeNode_free edges state facts.coherent facts.linked resident]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨child, included, named⟩ := (childFree_member _ name).mp member
  obtain ⟨edge, selected, included⟩ := List.mem_flatMap.mp included
  have original := (List.mem_filter.mp (canonicalEdges_member _ edge selected)).1
  rw [closed edge original child included] at named
  cases named

/-- Every union branch preserves closed operands, including ordinary cache readback. -/
theorem makeUnion_closed [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state values) (closed : ClosedValues values) :
    (run (makeUnion values) state).1.free = [] := by
  have normalizedInputs : Values state (distinctNodes (values.flatMap unionMembers)) := by
    intro value member
    obtain ⟨outer, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available outer (inputs outer included) value inner
  have normalizedClosed : ClosedValues (distinctNodes (values.flatMap unionMembers)) := by
    intro value member
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name named
    obtain ⟨original, included, present⟩ := (normalized_free state facts.coherent values inputs name).mp ⟨value, member, named⟩
    rw [closed original included] at present
    cases present
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, Value.free]
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using normalizedClosed first (by simp [normalized])
      | cons second tail =>
          have memberInputs : Values state (first :: second :: tail) := by simpa only [normalized] using normalizedInputs
          have memberClosed : ClosedValues (first :: second :: tail) := by simpa only [normalized] using normalizedClosed
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have edgeInputs : Edges state edges := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (memberInputs value member).resident) ordinary
              have edgeClosed : ClosedEdges edges := by
                intro edge member child included
                apply List.eq_nil_iff_forall_not_mem.mpr
                intro name named
                obtain ⟨value, present, free⟩ := (ordinaryEdges_free state facts.coherent _ edges
                  (fun value member => (memberInputs value member).resident) ordinary name).mp ⟨edge, member, child, included, named⟩
                rw [memberClosed value present] at free
                cases free
              simpa only [makeUnion, normalized, ordinary] using makeNode_closed edges state facts edgeInputs edgeClosed
          | none =>
              have built := makeUnion_available values state facts.coherent facts.cached inputs
              let members := first :: second :: tail
              let key := InternedBinderProtocol.NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have resultAvailable : Available after result := by simpa only [makeUnion, normalized, ordinary, run] using built.2.2
              have afterCoherent : Coherent after := by simpa only [makeUnion, normalized, ordinary, run] using built.1
              have afterInputs : Values after members := by
                intro value member
                simpa only [makeUnion, normalized, ordinary, run] using
                  available_after_run (makeUnion values) state facts.coherent.valid (memberInputs value member)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state facts.coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have resultClosed : result.free = [] := by
                apply List.eq_nil_iff_forall_not_mem.mpr
                intro name named
                obtain ⟨value, member, named⟩ := (union_readback_free after afterCoherent members actual result
                  fields resultAvailable afterInputs name).mp named
                rw [memberClosed value member] at named
                cases named
              simpa only [makeUnion, normalized, ordinary, run] using resultClosed

mutual
/-- Closed lexical inputs produce a closed completed binder-free source value. -/
theorem build_closed [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (closed : ClosedValues environment)
    (free : BinderFree expression) :
    ∃ value after, build expression environment state = .done value after ∧ value.free = [] := by
  cases expression with
  | empty => exact ⟨_, _, by rw [build], rfl⟩
  | var index =>
      cases found : environment[index]? with
      | none => exact ⟨_, _, by rw [build, found], rfl⟩
      | some value => exact ⟨value, state, by simp only [build, found, Option.getD_some], closed value (List.mem_of_getElem? found)⟩
  | binder => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      obtain ⟨values, after, done, children⟩ := buildEdges_closed edges environment state facts inputs closed free
      have verified := buildEdges_verified edges environment state facts inputs
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      exact ⟨_, (run (makeNode values) after).2, by simp only [build, done, Outcome.bind, work],
        makeNode_closed values after afterFacts (verified.result values after done) children⟩
  | union members =>
      simp only [BinderFree] at free
      obtain ⟨values, after, done, children⟩ := buildMany_closed members environment state facts inputs closed free
      have verified := buildMany_verified members environment state facts inputs
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      exact ⟨_, (run (makeUnion values) after).2, by simp only [build, done, Outcome.bind, work],
        makeUnion_closed values after afterFacts (verified.result values after done) children⟩
termination_by sizeOf expression

/-- Ordered binder-free children retain their closed inputs through preceding effects. -/
theorem buildMany_closed [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (closed : ClosedValues environment)
    (free : ManyBinderFree expressions) :
    ∃ values after, buildMany expressions environment state = .done values after ∧ ClosedValues values := by
  cases expressions with
  | nil => exact ⟨[], state, by rw [buildMany], by simp [ClosedValues]⟩
  | cons expression rest =>
      simp only [ManyBinderFree] at free
      obtain ⟨value, middle, done, valueClosed⟩ := build_closed expression environment state facts inputs closed free.1
      have verified := build_verified expression environment state facts inputs
      have middleFacts : Facts middle := by simpa only [done, Outcome.state] using verified.facts
      have middleInputs : Values middle environment := by
        intro value member
        simpa only [done, Outcome.state] using verified.available value (inputs value member)
      obtain ⟨values, after, tail, valuesClosed⟩ := buildMany_closed rest environment middle middleFacts middleInputs closed free.2
      refine ⟨value :: values, after, by simp only [buildMany, done, Outcome.bind, tail], ?_⟩
      intro child member
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using valueClosed
      · exact valuesClosed child member
termination_by sizeOf expressions

/-- Actual edge interning retains the exact closed ordered child records. -/
theorem buildEdges_closed [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (closed : ClosedValues environment)
    (free : EdgesBinderFree expressions) :
    ∃ edges after, buildEdges expressions environment state = .done edges after ∧ ClosedEdges edges := by
  cases expressions with
  | nil => exact ⟨[], state, by rw [buildEdges], by simp [ClosedEdges]⟩
  | cons expression rest =>
      cases expression with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          obtain ⟨values, middle, done, valuesClosed⟩ := buildMany_closed children environment state facts inputs closed free.1
          have verified := buildMany_verified children environment state facts inputs
          have middleFacts : Facts middle := by simpa only [done, Outcome.state] using verified.facts
          have available := verified.result values middle done
          let edge := run (makeEdge symbol constraint values) middle
          have built := edge_verified symbol constraint values middle middleFacts available
          have edgeClosed : ClosedValues edge.1.children := by
            rw [makeEdge_children symbol constraint values middle middleFacts.coherent middleFacts.cached available]
            exact valuesClosed
          have laterInputs : Values edge.2 environment := by
            intro value member
            exact built.available value (by simpa only [done, Outcome.state] using verified.available value (inputs value member))
          obtain ⟨edges, after, tail, edgesClosed⟩ := buildEdges_closed rest environment edge.2 built.facts laterInputs closed free.2
          refine ⟨edge.1 :: edges, after, ?_, ?_⟩
          · simp only [buildEdges, done, Outcome.bind, work]
            change (buildEdges rest environment edge.2).bind _ = _
            simp only [tail, Outcome.bind]
            rfl
          · intro selected member
            rcases List.mem_cons.mp member with same | member
            · simpa only [same] using edgeClosed
            · exact edgesClosed selected member
termination_by sizeOf expressions
end

end MicroCFTA.MergedColdReaderClosedInputs
