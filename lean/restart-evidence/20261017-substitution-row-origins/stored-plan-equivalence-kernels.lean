import MicroCFTA.SourceCurrentStoredPlanEquivalence
import MicroCFTA.InternedFreshOrdinaryFacts

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.StoredPlanEquivalenceKernels
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment encode input leaves)
open InternedStoredSubstitutionRebind (resolve replacement)
open InternedNestedProvenance (Values)
open SourceCurrentStoredPlanEquivalence

private def old : Reference := .uninterned 42
private def environment : Environment Nat Bool := replacement old (.reference .depth)
private def plan : Syntax Nat Bool :=
  .node [.mk 3 false [.var 0, .binder false (.node [.mk 4 true [.var 0, .var 1]])]]
private def nested : Value Nat Bool → Bool
  | .node _ [row] _ _ => match row.children with
    | [_, .mu ..] => true
    | _ => false
  | _ => false
private def observation : Option (Bool × Bool) :=
  match InternedFreshOrdinaryConstruction.build plan [.reference old] empty with
  | .done value _ => some (value.free.isEmpty, nested value)
  | .pending .. => none
set_option cbv.maxSteps 100000000 in
private theorem observed : observation = some (false, true) := by cbv

/-- A source-built open value retains a nested raw Mu while recapturing a shifted, duplicated leaf context. -/
theorem constructed_nested_recapture :
    ∃ value before,
      InternedFreshOrdinaryConstruction.build plan [.reference old] empty = .done value before ∧
      value.free ≠ [] ∧ nested value = true ∧
      ∀ current,
        InternedFreshOrdinaryConstruction.build
          (encode (.empty :: (leaves value ++ leaves value)) [] value)
          ((.empty :: (leaves value ++ leaves value)).map (input environment)) current =
            InternedFreshOrdinaryStoredSubstitution.execute value environment current := by
  have computed := observed
  cases actual : InternedFreshOrdinaryConstruction.build plan [.reference old] empty with
  | pending key after => simp [observation, actual] at computed
  | done value before =>
    have inputs : Values (empty : State Nat Bool) [.reference old] := by
      intro item member
      cases List.mem_singleton.mp member
      exact InternedNestedProvenance.ordinary_available empty 42
    have physical := InternedFreshOrdinaryFacts.build_verified plan [.reference old] empty empty_facts inputs
    have available := physical.result value before actual
    have coherent : Coherent before := by simpa only [actual, Outcome.state] using physical.facts.coherent
    have captures : Values before (.empty :: (leaves value ++ leaves value)) := by
      intro leaf member
      rcases List.mem_cons.mp member with rfl | later
      · exact InternedProbeProvenance.empty_available before
      · rcases List.mem_append.mp later with first | second
        · exact InternedStoredSubstitution.leaves_available value before available leaf first
        · exact InternedStoredSubstitution.leaves_available value before available leaf second
    simp only [observation, actual, Option.some.injEq, Prod.mk.injEq] at computed
    refine ⟨value, before, rfl, ?_, computed.2, ?_⟩
    · intro closed
      simp [closed] at computed
    · intro current
      exact recapture _ value environment before current coherent captures available
        (fun leaf member => List.mem_cons_of_mem _ (List.mem_append_left _ member))

/-- Distinct capture layouts and duplicate lexical names resolve to the first local value at any current heap. -/
theorem shadowed_independent_contexts (current : State Nat Bool) :
    InternedFreshOrdinaryConstruction.build
      (encode [.reference .depth, .empty] [.depth, .depth] (.reference .depth : Value Nat Bool))
      ([.reference (.uninterned 17), .empty] ++ [.reference .depth, .empty].map (input (fun _ => none))) current =
        InternedFreshOrdinaryStoredSubstitution.execute (.reference .depth)
          (replacement .depth (.reference (.uninterned 17))) current := by
  have firstAvailable : Values (empty : State Nat Bool) [.reference .depth, .empty] := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact InternedNestedProvenance.depth_available empty
    · exact InternedProbeProvenance.empty_available empty
  have secondAvailable : Values (empty : State Nat Bool)
      [.empty, .reference (.uninterned 17), .reference .depth] := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact InternedProbeProvenance.empty_available empty
    · exact InternedNestedProvenance.ordinary_available empty 17
    · exact InternedNestedProvenance.depth_available empty
  have plans := encode_equivalent [.reference .depth, .empty]
    [.empty, .reference (.uninterned 17), .reference .depth] (.reference .depth : Value Nat Bool)
    [.depth, .depth] [] [.reference (.uninterned 17), .empty] []
    (fun _ => none) (replacement .depth (.reference (.uninterned 17))) empty empty_correct.1
    firstAvailable secondAvailable (by simp [leaves, Value.free]) (by simp [leaves, Value.free])
    rfl rfl (by
      intro name
      rw [InternedStoredSubstitutionRebind.resolve_cons]
      simp only [resolve, List.findIdx?_nil]
      by_cases same : name = .depth
      · subst name
        simp [replacement]
      · have other : (.depth : Reference) ≠ name := Ne.symm same
        simp [replacement, same, other])
  have compared := InternedFreshOrdinaryPlanEquivalence.build_exact _ _ _ _ current plans
  have captured := recapture [.empty, .reference (.uninterned 17), .reference .depth]
    (.reference .depth : Value Nat Bool) (replacement .depth (.reference (.uninterned 17))) empty current
    empty_correct.1 secondAvailable (InternedNestedProvenance.depth_available empty) (by simp [leaves, Value.free])
  exact compared.trans (by simpa only [List.nil_append] using captured)

end MicroCFTA.StoredPlanEquivalenceKernels
