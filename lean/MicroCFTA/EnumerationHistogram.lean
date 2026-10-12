import MicroCFTA.EnumerationDecrease
import MicroCFTA.HeightOrder

/-!
# A decreasing count of pending term heights

The height range is fixed. Each expansion removes one pending term at its
selected height and can add any finite number of smaller pending terms.
-/

namespace MicroCFTA.EnumerationHistogram
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction EnumerationOutConstruction EnumerationDecrease

/-- The allocated pending graph variables assigned terms of one height. -/
noncomputable def workAt (state : State Symbol Guard) (assignment : Nat → Term Symbol) (height : Nat) : List Nat := by
  classical
  exact (List.range state.values.length).filter fun uv => decide (GraphPending state uv ∧ (assignment uv).height = height)

/-- The finite number of pending graph variables at each term height. -/
noncomputable def histogram (state : State Symbol Guard) (assignment : Nat → Term Symbol) (height : Nat) : Nat :=
  (workAt state assignment height).length

/-- A pending graph variable has a stored array position. -/
theorem graphPending_inside (state : State Symbol Guard) (uv : Nat) (pending : GraphPending state uv) : uv < state.values.length := by
  obtain ⟨node, scs, stored⟩ := pending
  exact (List.getElem?_eq_some_iff.mp stored).1

/-- Membership of a height list is exactly a pending graph slot of that height. -/
theorem mem_workAt (state : State Symbol Guard) (assignment : Nat → Term Symbol) (height uv : Nat) :
    uv ∈ workAt state assignment height ↔ GraphPending state uv ∧ (assignment uv).height = height := by
  classical
  simp only [workAt, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨And.right, fun both => ⟨graphPending_inside state uv both.1, both⟩⟩

/-- Height lists contain each stored index once. -/
theorem workAt_nodup (state : State Symbol Guard) (assignment : Nat → Term Symbol) (height : Nat) :
    (workAt state assignment height).Nodup := by
  classical
  exact List.nodup_range.filter _

/-- Changing only fresh assignment values leaves all old height lists unchanged. -/
theorem workAt_assignment (state : State Symbol Guard) (aligned : SupplyAligned state)
    (left right : Nat → Term Symbol) (agree : ∀ uv < state.counter, left uv = right uv) (height : Nat) :
    workAt state left height = workAt state right height := by
  classical
  apply List.filter_congr
  intro uv member
  have inside : uv < state.counter := by rw [aligned]; exact List.mem_range.mp member
  rw [agree uv inside]

/-- Every post-expansion height at or above the selected height is a subset of old work. -/
theorem workAt_subset (before after : State Symbol Guard) (assignment extended : Nat → Term Symbol) (height cutoff : Nat)
    (aligned : SupplyAligned before) (agree : ∀ uv < before.counter, extended uv = assignment uv)
    (origin : HighOrigin extended cutoff before after) (high : cutoff ≤ height) :
    workAt after extended height ⊆ workAt before assignment height := by
  intro uv member
  obtain ⟨pending, exactHeight⟩ := (mem_workAt after extended height uv).mp member
  have old := origin uv (by omega) pending
  have inside : uv < before.counter := by rw [aligned]; exact graphPending_inside before uv old
  exact (mem_workAt before assignment height uv).mpr ⟨old, by simpa [agree uv inside] using exactHeight⟩

/-- Deleting the selected index makes its height count strictly smaller. -/
theorem histogram_strict (before after : State Symbol Guard) (assignment extended : Nat → Term Symbol) (uv : Nat)
    (aligned : SupplyAligned before) (agree : ∀ index < before.counter, extended index = assignment index)
    (origin : HighOrigin extended (assignment uv).height before after) (pending : GraphPending before uv)
    (removed : ¬GraphPending after uv) : histogram after extended (assignment uv).height < histogram before assignment (assignment uv).height := by
  have included := workAt_subset before after assignment extended (assignment uv).height (assignment uv).height aligned agree origin (Nat.le_refl _)
  have member := (mem_workAt before assignment (assignment uv).height uv).mpr ⟨pending, rfl⟩
  have erased : workAt after extended (assignment uv).height ⊆ (workAt before assignment (assignment uv).height).erase uv := by
    intro index listed
    apply (List.Nodup.mem_erase_iff (workAt_nodup before assignment (assignment uv).height)).mpr
    refine ⟨?_, included listed⟩
    intro same
    subst index
    exact removed ((mem_workAt after extended (assignment uv).height uv).mp listed).1
  have bound := (workAt_nodup after extended (assignment uv).height).length_le_of_subset erased
  rw [List.length_erase_of_mem member] at bound
  unfold histogram
  have positive := List.length_pos_of_mem member
  omega

/-- Each successful witnessed expansion strictly decreases the finite height histogram. -/
theorem enumerateOut_histogram (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment extended : Nat → Term Symbol) (fuel uv bound : Nat) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (ready : Ready uv before) (proper : ProperState before) (pending : GraphPending before uv)
    (agree : ∀ index < before.counter, extended index = assignment index) (inside : (assignment uv).height < bound)
    (success : Success (enumerateOut graph fuel uv) before fragment after)
    (satisfies : Satisfies (Accepted graph meaning) meaning extended after) :
    HeightOrder.Below bound (histogram after extended) (histogram before assignment) := by
  obtain ⟨origin, removed⟩ := enumerateOut_height_origin graph meaning complete correct extended fuel uv before after fragment ready proper success satisfies
  have originOld : HighOrigin extended (assignment uv).height before after := by simpa [agree uv ready.inside] using origin
  apply HeightOrder.below_of_decrease bound (histogram after extended) (histogram before assignment) (assignment uv).height inside
  · exact histogram_strict before after assignment extended uv ready.safe.1.aligned agree originOld pending removed
  · intro height above below
    exact (workAt_nodup after extended height).length_le_of_subset
      (workAt_subset before after assignment extended height (assignment uv).height ready.safe.1.aligned agree originOld (by omega))

/-- All pending graph terms lie below the fixed initial height bound. -/
def BoundedWork (bound : Nat) (state : State Symbol Guard) (assignment : Nat → Term Symbol) : Prop :=
  ∀ uv, GraphPending state uv → (assignment uv).height < bound

/-- Actual expansion preserves the fixed height range while it changes the lower counts. -/
theorem enumerateOut_bounded (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment extended : Nat → Term Symbol) (fuel uv bound : Nat) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (ready : Ready uv before) (proper : ProperState before) (pending : GraphPending before uv)
    (agree : ∀ index < before.counter, extended index = assignment index) (bounded : BoundedWork bound before assignment)
    (success : Success (enumerateOut graph fuel uv) before fragment after)
    (satisfies : Satisfies (Accepted graph meaning) meaning extended after) : BoundedWork bound after extended := by
  have origin := (enumerateOut_height_origin graph meaning complete correct extended fuel uv before after fragment ready proper success satisfies).1
  have selected := bounded uv pending
  intro index afterPending
  by_cases small : (extended index).height < bound
  · exact small
  · have old := origin index (by rw [agree uv ready.inside]; omega) afterPending
    have inside : index < before.counter := by rw [ready.safe.1.aligned]; exact graphPending_inside before index old
    rw [agree index inside]
    exact bounded index old

end MicroCFTA.EnumerationHistogram
