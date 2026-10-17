import MicroCFTA.SourceRecursiveIntersectionNative
import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCompile

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.JointNativeProbe
open Cache InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
local notation "Heap" => InternedConstructorTemplates.State Nat Bool
local notation "V" => Value Nat Bool
private abbrev S := Syntax Nat Bool
private def leaf (guard : Bool) : S := .node [.mk 0 guard []]
private def unary (guard : Bool) (child : S) : S := .node [.mk 1 guard [child]]
private def loops : List (S × S) :=
  [(.binder false (.var 0), leaf false),
   (.binder false (.union [leaf true, unary true (.var 0)]), unary false (leaf true))]
private def selected (index : Nat) := (loops[index]?).getD (.empty, .empty)
private def first (index : Nat) := InternedFreshOrdinaryConstruction.build (selected index).1 [] (empty : Heap)
private def left (index : Nat) : V := match first index with | .done value _ => value | .pending .. => .empty
private def second (index : Nat) := InternedFreshOrdinaryConstruction.build (selected index).2 [] (first index).state
private def right (index : Nat) : V := match second index with | .done value _ => value | .pending .. => .empty
private def source (index : Nat) := (second index).state
private def initial (index : Nat) := SourceRecursiveIntersectionThunks.initial 8
  (⟨source index, Cache.emptyState⟩ : SourceRecursiveIntersectionKernel.Machine Nat Bool)
private def code (index : Nat) := requestNode IntersectionEmptyDomain.emptyDomain (right index) (left index)
private def cold (index : Nat) := SourceRecursiveIntersectionNative.execute true Bool.and 128 (code index) (initial index)
private def tag {A} : SourceRecursiveIntersectionNative.Outcome 8 Nat Bool A → Nat
  | .done .. => 0 | .yielded .. => 1 | .failed .. => 2 | .blocked .. => 3
private def result (index : Nat) : V := match cold index with | .done value _ => value | _ => .empty
private def warm (index : Nat) := SourceRecursiveIntersectionNative.execute true Bool.and 2 (code index) (cold index).state
private def describe (index : Nat) :=
  (index, tag (cold index), (result index).referenceOf,
    (source index).nodes.next, (cold index).state.machine.heap.nodes.next,
    (cold index).state.nodes.next, (cold index).state.edges.next, tag (warm index))
#eval describe 0
#eval describe 1

private def annotation (guard : Bool) : Prop := guard = true
private def after (index : Nat) := (cold index).state

set_option cbv.maxSteps 100000000 in
private theorem cold_zero : cold 0 = .done .empty (after 0) := by cbv
set_option cbv.maxSteps 100000000 in
private theorem cold_one : cold 1 = .done (right 1) (after 1) := by cbv
set_option cbv.maxSteps 100000000 in
private theorem warm_zero : warm 0 = .done .empty (after 0) := by cbv
set_option cbv.maxSteps 100000000 in
private theorem warm_one : warm 1 = .done (right 1) (after 1) := by cbv

private def outerEntry := match right 1 with | .node entry _ _ _ => entry | _ => ⟨0, .node []⟩
private def outerRow := match nodeEdges (right 1) with | row :: _ => row.entry | _ => ⟨0, ⟨0, [], true⟩⟩
private def innerValue := match nodeEdges (right 1) with | .mk _ (value :: _) :: _ => value | _ => .empty
private def innerEntry := match innerValue with | .node entry _ _ _ => entry | _ => ⟨0, .node []⟩
private def innerRow := match nodeEdges innerValue with | row :: _ => row.entry | _ => ⟨0, ⟨0, [], false⟩⟩
private theorem right_shape : right 1 = .node outerEntry [.mk outerRow [.node innerEntry [.mk innerRow []] 0 []]] 0 [] := by cbv
private theorem outer_bad : outerRow.key.constraint = false := by cbv
private theorem inner_good : innerRow.key.constraint = true := by cbv

private theorem right_profile : SourceCurrentConstrainedCapGuardDepth.profile annotation (right 1) = some 1 := by
  rw [right_shape]
  simp only [SourceCurrentConstrainedCapGuardDepth.profile, SourceCurrentConstrainedCapGuardDepth.rows,
    SourceCurrentConstrainedCapGuardDepth.children, SourceCurrentConstrainedCapGuardDepth.guardCost,
    annotation, outer_bad, inner_good, Bool.false_eq_true, ↓reduceIte,
    SourceCurrentConstrainedCapGuardDepth.join, SourceCurrentConstrainedCapGuardDepth.raise]
  rfl

/-- A real constrained ordinary input and a real recursive operand complete cold execution, then an exact warm hit returns the same value and whole native state. -/
theorem productive_mixed_cold_then_warm :
    (∃ firstHeap, first 1 = .done (left 1) firstHeap ∧ second 1 = .done (right 1) (source 1)) ∧
      SourceRecursiveIntersectionNative.execute true Bool.and 128 (code 1) (initial 1) = .done (right 1) (after 1) ∧
      SourceCurrentConstrainedCapGuardDepth.profile annotation (right 1) = some 1 ∧
      SourceCurrentConstrainedCap.Cap annotation 1 (right 1) ∧
      ¬SourceEqualityAnnotationLanguage.Annotated annotation (right 1) ∧
      SourceRecursiveIntersectionNative.execute true Bool.and 2 (code 1) (after 1) = .done (right 1) (after 1) := by
  have built : ∃ firstHeap, first 1 = .done (left 1) firstHeap ∧ second 1 = .done (right 1) (source 1) := by
    refine ⟨(first 1).state, ?_, ?_⟩ <;> cbv
  have bounded := SourceCurrentConstrainedCapGuardDepth.cap_of_profile annotation 1 (right 1)
    (by simp [right_profile, SourceCurrentConstrainedCapGuardDepth.Within])
  have nonplain : ¬SourceEqualityAnnotationLanguage.Annotated annotation (right 1) := by
    intro plain
    have zero := (SourceCurrentConstrainedCapGuardDepth.zero_iff_annotated annotation (right 1)).mpr plain
    simp [right_profile, SourceCurrentConstrainedCapGuardDepth.Within] at zero
  exact ⟨built, cold_one, right_profile, bounded, nonplain, warm_one⟩

/-- The mixed unproductive cycle also completes and its exact warm hit retains the full state. -/
theorem unproductive_mixed_cold_then_warm :
    SourceRecursiveIntersectionNative.execute true Bool.and 128 (code 0) (initial 0) = .done .empty (after 0) ∧
      SourceRecursiveIntersectionNative.execute true Bool.and 2 (code 0) (after 0) = .done .empty (after 0) :=
  ⟨cold_zero, warm_zero⟩

#print axioms productive_mixed_cold_then_warm
#check @productive_mixed_cold_then_warm
#print axioms unproductive_mixed_cold_then_warm
#check @unproductive_mixed_cold_then_warm
end MicroCFTA.JointNativeProbe
