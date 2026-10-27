import MicroCFTA.EnumerationFlatCore
import MicroCFTA.EnumerationExpandableIndex

/-!
# Cached state across the union-find representation change

Both indexes remain literal functions. Their correctness is separate from
core correspondence. In particular, raw and canonical waiting counts differ.
-/

namespace MicroCFTA.EnumerationFlatCached

/-- The flat core retains both cached indexes at the same raw addresses. -/
structure Cached (Symbol Guard : Type) where
  core : EnumerationFlatState.State Symbol Guard
  expandable : Nat → Bool
  waiting : EnumerationWaitingIndex.Waiting

/-- Correspondence keeps both complete indexes and relates the complete core. -/
structure Related (flat : Cached Symbol Guard)
    (earlier : EnumerationExpandableIndex.Cached Symbol Guard) : Prop where
  core : EnumerationFlatState.Related flat.core earlier.core
  expandable : flat.expandable = earlier.expandable
  waiting : flat.waiting = earlier.waiting

/-- Replace the core without changing the cached indexes. -/
def frame (core : EnumerationFlatState.State Symbol Guard) (state : Cached Symbol Guard) :
    Cached Symbol Guard := {state with core := core}

/-- Related returned cores retain the exact indexes of the related input caches. -/
theorem frame_related (related : Related flat earlier)
    (cores : EnumerationFlatState.Related nextFlat nextEarlier) :
    Related (frame nextFlat flat) (EnumerationExpandableIndex.frame nextEarlier earlier) :=
  ⟨cores, related.expandable, related.waiting⟩

/-- Initialize the same root slot and the same source-scan expandable flag. -/
def initial (graph : EnumerationState.Graph Symbol Guard) (root : Nat) : Cached Symbol Guard :=
  ⟨EnumerationFlatState.initial root,
    fun uv => if uv = 0 then
      EnumerationSchedule.candidate graph (.unenumerated (some root) []) else false,
    fun _ => none⟩

/-- Initialization relates both complete caches without an index assumption. -/
theorem initial_related (graph : EnumerationState.Graph Symbol Guard) (root : Nat) :
    Related (initial graph root) (EnumerationExpandableIndex.initial graph root) :=
  ⟨EnumerationFlatState.initial_related root, rfl, rfl⟩

end MicroCFTA.EnumerationFlatCached
