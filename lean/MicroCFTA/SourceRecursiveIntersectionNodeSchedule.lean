import MicroCFTA.SourceRecursiveIntersectionRowsSchedule
import MicroCFTA.SourceRecursiveIntersectionInputView

/-!
# Exact semantic node steps from actual ordered row requests

The physical and semantic hash joins retain the same ordered row pairs.
This includes duplicate occurrences and reversed right buckets. Local
edge correspondence then passes through actual node normalization.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionScheduleConstructors (Corresponds EdgeCorresponds)
open SourceRecursiveIntersectionInputView (row)

/-- The actual symbol hash join has exactly the mapped semantic row order. -/
theorem joined_rows [DecidableEq Symbol] (holds : Guard → Term Symbol → Bool)
    (left right : List (EdgeValue Symbol Guard)) :
    IntersectSchedule.joined (left.map (row holds)) (right.map (row holds)) =
      (pairs left right).map (fun pair => (row holds pair.1, row holds pair.2)) := by
  simp only [IntersectSchedule.joined, pairs, SymbolicHashJoin.hashJoin_exact, List.flatMap_map,
    List.map_flatMap, List.filter_map, List.map_reverse, List.map_map, Function.comp_def, row]
  rfl

/-- Actual node work has exactly the semantic ordered-row result under local edge correspondence. -/
theorem node_schedule [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (done : node emptyGuard conjoin (call domain) left right state = .done value state)
    (holds : Guard → Term Symbol → Bool) (view : IntersectSchedule.View Symbol) (fuel : Nat)
    (children : ∀ pair ∈ pairs left right, ∀ result,
      edge emptyGuard conjoin (call domain) pair.1 pair.2 state = .done result state → ∃ shape,
        IntersectSchedule.edge view fuel (SourceRecursiveIntersectionSchedule.domain domain.key)
          (row holds pair.1) (row holds pair.2) = .ok shape ∧ EdgeCorresponds holds result shape) :
    ∃ shape,
      (IntersectSchedule.walk (fun pair => IntersectSchedule.edge view fuel (SourceRecursiveIntersectionSchedule.domain domain.key)
        pair.1 pair.2) (IntersectSchedule.joined (left.map (row holds)) (right.map (row holds)))).map Shape.alternatives = .ok shape ∧
      Corresponds holds value shape := by
  let action := fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => IntersectSchedule.edge view fuel
    (SourceRecursiveIntersectionSchedule.domain domain.key) (row holds pair.1) (row holds pair.2)
  obtain ⟨shapes, walked, meanings⟩ := node_schedule_body emptyGuard conjoin call calls replay domain left right state valid
    known leftResident rightResident value done holds action children
  refine ⟨.alternatives shapes, ?_, meanings⟩
  rw [joined_rows, IntersectSchedule.walk_map]
  change Except.map _ (IntersectSchedule.walk action (pairs left right)) = _
  rw [walked]
  rfl

end MicroCFTA.SourceRecursiveIntersectionKernel
