import MicroCFTA.SourceRecursiveIntersectionRowsSchedule
import MicroCFTA.SourceRecursiveIntersectionScheduleOriginals

/-!
# Exact semantic edge steps from actual completed edge calls

The semantic edge worker receives the actual ordered child inputs and full
guards. Corresponding recursive child calls supply its bounded result.
Arity mismatch agrees directly with the empty semantic shape.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionScheduleConstructors (Corresponds EdgeCorresponds)
open SourceRecursiveIntersectionInputView (inputOf row)

/-- Actual completed edge work has the same semantic edge outcome under local recursive correspondence. -/
theorem edge_schedule [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (value : EdgeValue Symbol Guard) (done : edge emptyGuard conjoin (call domain) left right state = .done value state)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (view : IntersectSchedule.View Symbol) (fuel : Nat)
    (children : ∀ pair ∈ left.children.zip right.children, ∀ child,
      call domain pair.1 pair.2 state = .done child state → ∃ shape,
        IntersectSchedule.run view fuel (SourceRecursiveIntersectionSchedule.domain domain.key)
          (inputOf pair.1) (inputOf pair.2) = .ok shape ∧ Corresponds holds child shape) :
    ∃ shape, IntersectSchedule.edge view (fuel + 1) (SourceRecursiveIntersectionSchedule.domain domain.key)
      (row holds left) (row holds right) = .ok shape ∧ EdgeCorresponds holds value shape := by
  by_cases arity : left.children.length = right.children.length
  · let action := fun pair : Value Symbol Guard × Value Symbol Guard => IntersectSchedule.run view fuel
      (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf pair.1) (inputOf pair.2)
    obtain ⟨shapes, walked, meanings⟩ := edge_schedule_body emptyGuard conjoin call calls replay domain left right
      state valid known leftResident rightResident arity value done holds conjoined action children
    refine ⟨.branch ⟨left.entry.key.symbol, fun term =>
      holds left.entry.key.constraint term = true ∧ holds right.entry.key.constraint term = true⟩ shapes, ?_, meanings⟩
    rw [IntersectSchedule.edge.eq_2]
    simp only [row, List.length_map, arity, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [List.zip_map, IntersectSchedule.walk_map]
    change Except.map _ (IntersectSchedule.walk action (left.children.zip right.children)) = _
    rw [walked]
    rfl
  · refine ⟨.empty, ?_, edge_schedule_mismatch emptyGuard conjoin (call domain) left right state valid arity value state done holds⟩
    rw [IntersectSchedule.edge.eq_2]
    simp only [row, List.length_map, arity, ne_eq, not_false_eq_true, ↓reduceIte]

end MicroCFTA.SourceRecursiveIntersectionKernel
