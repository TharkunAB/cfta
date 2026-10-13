import MicroCFTA.InternedRetainedCompletion
import MicroCFTA.InternedLiveEdges
import MicroCFTA.InternedNestedSpecialization

/-!
# Source reference retention through normalized root unions

A retained source slot can occur as a bare variable, a unary node edge,
or an alternative below root unions. Actual union normalization preserves
its free name through edge merging, singleton collapse, and cache hits.
-/
namespace MicroCFTA.InternedUnionReferences
open InternedConstructorTemplates InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedRecordCoherence InternedProbeProvenance InternedFreshProbeKeys InternedLiveEdges
open InternedNormalizationFree InternedNestedRootReferences InternedNestedSpecialization
open InternedBinderProtocol (Reference)

/-- A source variable remains visible through declared ordinary edges and union alternatives. -/
inductive Retains (index : Nat) : Syntax Symbol Guard → Prop where
  | var : Retains index (.var index)
  | node (edges : List (EdgeSyntax Symbol Guard)) (symbol : Symbol) (constraint : Guard)
      (member : .mk symbol constraint [.var index] ∈ edges) : Retains index (.node edges)
  | union (members : List (Syntax Symbol Guard)) (child : Syntax Symbol Guard)
      (member : child ∈ members) (retained : Retains index child) : Retains index (.union members)

/-- Every completed source child contributes its actual result to the parent operand list. -/
theorem buildMany_member_result [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (live : Live before)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard)
    (completed : buildMany expressions environment before = .done values final)
    (selected : Syntax Symbol Guard) (member : selected ∈ expressions) :
    ∃ start value finish, build selected environment start = .done value finish ∧ value ∈ values ∧
      Facts start ∧ Values start environment ∧ Live start := by
  cases expressions with
  | nil => cases member
  | cons first rest =>
      simp only [buildMany] at completed
      obtain ⟨head, middle, firstDone, later⟩ := bind_done _ _ _ _ completed
      obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ later
      simp only [Outcome.done.injEq] at assembled
      obtain ⟨rfl, rfl⟩ := assembled
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨before, head, middle, firstDone, List.mem_cons_self, facts, inputs, live⟩
      · have verified := build_verified first environment before facts inputs
        have middleFacts : Facts middle := by simpa only [firstDone, Outcome.state] using verified.facts
        have middleInputs : Values middle environment := by
          intro value included
          simpa only [firstDone, Outcome.state] using verified.available value (inputs value included)
        have middleLive : Live middle := by simpa only [firstDone, Outcome.state] using build_live first environment before live
        obtain ⟨start, value, finish, selectedDone, included, good, available, living⟩ :=
          buildMany_member_result rest environment middle middleFacts middleInputs middleLive tail last tailDone selected inRest
        exact ⟨start, value, finish, selectedDone, List.mem_cons_of_mem _ included, good, available, living⟩
termination_by expressions.length

/-- The source declaration derives actual output metadata through every union normalization branch. -/
theorem build_retains [DecidableEq (EdgeKey Symbol Guard)] (retained : Retains index expression)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (live : Live before) (name : Reference)
    (lookup : environment[index]?.getD .empty = .reference name)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : build expression environment before = .done value final) : name ∈ value.free := by
  induction retained generalizing environment before value final with
  | var =>
      simp only [build, lookup, Outcome.done.injEq] at completed
      simp [← completed.1, Value.free]
  | node edges symbol constraint member =>
      exact build_node_reference edges environment before facts inputs value final completed symbol constraint index name member lookup
  | union members child member retained ih =>
      simp only [build] at completed
      obtain ⟨values, middle, childrenDone, parentDone⟩ := bind_done _ _ _ _ completed
      obtain ⟨start, selected, finish, selectedDone, included, good, available, living⟩ :=
        buildMany_member_result members environment before facts inputs live values middle childrenDone child member
      have named := ih environment start good available living lookup selected finish selectedDone
      have verified := buildMany_verified members environment before facts inputs
      have middleFacts : Facts middle := by simpa only [childrenDone, Outcome.state] using verified.facts
      have middleLive : Live middle := by simpa only [childrenDone, Outcome.state] using buildMany_live members environment before live
      have result := (makeUnion_free values middle middleFacts.coherent middleFacts.cached middleFacts.linked middleLive
        (verified.result values middle childrenDone) name).mpr ⟨selected, included, named⟩
      simp only [work, Outcome.done.injEq] at parentDone
      exact parentDone.1 ▸ result

end MicroCFTA.InternedUnionReferences
