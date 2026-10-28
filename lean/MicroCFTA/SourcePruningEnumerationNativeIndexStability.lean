import MicroCFTA.SourcePruningEnumerationFinalize

/-!
# Successful index and finalizer observations at larger bounds

The observed read-only representative lookups retain their exact result.
The proof needs no cache invariant or resource reservation.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeIndex
open EnumerationState EnumerationSchedule SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- A successful waiting-count pass retains its exact map at every larger bound. -/
theorem count_some_moreFuel
    (fuel extra : Nat) (forest : UnionFind.Forest) (change : Int)
    (scs : List Suspended) (waiting saved : EnumerationWaitingIndex.Waiting)
    (observed : count fuel forest change scs waiting = some saved) :
    count (fuel + extra) forest change scs waiting = some saved := by
  induction scs generalizing waiting with
  | nil => simpa only [count] using observed
  | cons sc rest ih =>
      simp only [count, Option.bind_eq_some_iff] at observed
      obtain ⟨representative, resolved, remaining⟩ := observed
      rw [count, SourceUnionFindRoot.root_moreFuel fuel extra forest sc.var representative resolved,
        Option.bind_some]
      exact ih _ remaining

/-- A successful indexed write retains its entire returned cache at every larger bound. -/
theorem write_some_moreFuel
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel extra target : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : write heap fuel target value gained lost before = some after) :
    write heap (fuel + extra) target value gained lost before = some after := by
  simp only [write, Option.bind_eq_some_iff, Option.some.injEq] at observed
  obtain ⟨flag, classified, removed, lostCounts, saved, gainedCounts, same⟩ := observed
  subst after
  simp only [write, classified, Option.bind_some,
    count_some_moreFuel fuel extra before.core.representatives (-1) lost before.waiting removed lostCounts,
    count_some_moreFuel fuel extra before.core.representatives 1 gained removed saved gainedCounts]

end MicroCFTA.SourcePruningEnumerationNativeIndex

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState EnumerationSchedule SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- A completed actual finalizer retains its entire cache at every larger index bound. -/
theorem run_some_moreFuel
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel extra target : Nat) (fragment : Fragments.Fragment Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : run heap fuel target fragment before = some after) :
    run heap (fuel + extra) target fragment before = some after := by
  simp only [run, Option.bind_eq_some_iff] at observed
  obtain ⟨old, stored, written⟩ := observed
  simp only [run, stored, Option.bind_some]
  exact SourcePruningEnumerationNativeIndex.write_some_moreFuel heap fuel extra target
    (.enumerated fragment) [] (references old) _ after written

end MicroCFTA.SourcePruningEnumerationFinalize
