import MicroCFTA.InternedStoredPlanBinderDepthProgress
import MicroCFTA.MergedPhysicalWarmup
import MicroCFTA.HeightOrder

/-!
# Canonical Mu identities and open-body depth counts

The issued supply gives a finite inventory. Only the canonical identity of
each complete Mu contributes to a count. Other reservations for the same
key contribute no duplicate. A new lower-depth Mu cannot increase a count
at or above the unfolded body's degree.
-/
namespace MicroCFTA.InternedMuDepthInventory
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedStoredPlanBinderDepth
open InternedStoredPlanBinderDepthProgress (Lower)
open InternedBinderProtocol (NodeKey)

/-- Read a complete Mu's body depth only at its own canonical issued identity. -/
def rankAt (state : State Symbol Guard) (identity : Nat) : Option Nat :=
  match state.nodes.issued identity with
  | none => none
  | some key => match state.nodeRecords key with
    | some (.mu entry body _ _) => if entry.identity = identity then some (valueDepth body) else none
    | _ => none

/-- A canonical Mu lookup is below the actual finite issued counter. -/
theorem rankAt_bound (state : State Symbol Guard) (valid : Cache.Valid state.nodes)
    (identity rank : Nat) (found : rankAt state identity = some rank) : identity < state.nodes.next := by
  cases issued : state.nodes.issued identity with
  | none => simp [rankAt, issued] at found
  | some key => exact valid.1 identity key issued

/-- A complete coherent Mu is read at the exact identity stored in its payload. -/
theorem rankAt_record (state : State Symbol Guard) (coherent : Coherent state)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : state.nodeRecords entry.key = some (.mu entry body depth ordinary)) :
    rankAt state entry.identity = some (valueDepth body) := by
  have resident := stored_resident state coherent entry.key _ present
  have canonical := resident_entry state coherent _ resident entry rfl
  have issued := (coherent.valid.2.2 entry.key entry canonical).2
  simp [rankAt, issued, present]

/-- The canonical lookup has exactly one actual resident Mu witness at the selected identity. -/
theorem rankAt_spec (state : State Symbol Guard) (coherent : Coherent state) (identity rank : Nat) :
    rankAt state identity = some rank ↔
      ∃ entry body depth ordinary, entry.identity = identity ∧
        state.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧ valueDepth body = rank := by
  constructor
  · intro found
    cases issued : state.nodes.issued identity with
    | none => simp [rankAt, issued] at found
    | some key =>
        cases present : state.nodeRecords key with
        | none => simp [rankAt, issued, present] at found
        | some value =>
            cases value with
            | empty | reference | node | union => simp [rankAt, issued, present] at found
            | mu entry body depth ordinary =>
                by_cases same : entry.identity = identity
                · have exactRank : valueDepth body = rank := by simpa [rankAt, issued, present, same] using found
                  exact ⟨entry, body, depth, ordinary, same, (stored_resident state coherent key _ present) entry rfl, exactRank⟩
                · simp [rankAt, issued, present, same] at found
  · rintro ⟨entry, body, depth, ordinary, rfl, present, rfl⟩
    exact rankAt_record state coherent entry body depth ordinary present

/-- Every complete Mu body lies below a fixed finite depth bound. -/
def Bounded (state : State Symbol Guard) (limit : Nat) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) → valueDepth body < limit

/-- The finite initial inventory supplies an upper bound without bounding future cached depth. -/
theorem initial_bounded (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state) :
    Bounded state (maximumDepth (nodeInventory state) + 1) := by
  intro key entry body depth ordinary present
  have available := facts.cached.nodes key _ present
  have member := MergedPhysicalWarmup.inventory_complete state facts.coherent key _ present
  have large := (maximumDepth_exact _ _).mp (Nat.le_refl _) (.mu entry body depth ordinary) member
  have small := value_le_cached body state facts.coherent (available.children body (by simp [children]))
  simp only [Value.depth] at large
  omega

/-- A strict new-body allocation bound preserves the fixed maximum degree. -/
theorem bounded_after (before after : State Symbol Guard) (limit rank : Nat)
    (bounded : Bounded before limit) (inside : rank < limit) (lower : Lower before rank after) : Bounded after limit := by
  intro key entry body depth ordinary present
  rcases lower key entry body depth ordinary present with old | small
  · exact bounded key entry body depth ordinary old
  · omega

/-- Test one unvisited canonical Mu at the selected open-body degree. -/
def unseenAt (state : State Symbol Guard) (seen : List Nat) (rank identity : Nat) : Bool :=
  decide (identity ∉ seen ∧ rankAt state identity = some rank)

/-- Count canonical unvisited Mu identities at one degree in the actual finite issued range. -/
def count (state : State Symbol Guard) (seen : List Nat) (rank : Nat) : Nat :=
  (List.range state.nodes.next).countP (unseenAt state seen rank)

/-- Enlarging the finite range adds no count when the predicate vanishes past the old bound. -/
theorem countP_extend (predicate : Nat → Bool) (small large : Nat) (inside : small ≤ large)
    (outside : ∀ identity, small ≤ identity → predicate identity = false) :
    (List.range large).countP predicate = (List.range small).countP predicate := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le inside
  rw [List.range_add, List.countP_append]
  have zero : ((List.range extra).map (small + ·)).countP predicate = 0 := by
    apply List.countP_eq_zero.mpr
    intro identity member
    obtain ⟨offset, _, rfl⟩ := List.mem_map.mp member
    exact Bool.eq_false_iff.mp (outside _ (by omega))
  omega

/-- A count can be compared in any larger finite identity range. -/
theorem count_extend (state : State Symbol Guard) (valid : Cache.Valid state.nodes)
    (seen : List Nat) (rank large : Nat) (inside : state.nodes.next ≤ large) :
    (List.range large).countP (unseenAt state seen rank) = count state seen rank := by
  apply countP_extend _ _ large inside
  intro identity outside
  apply Bool.eq_false_iff.mpr
  intro selected
  have included : identity ∉ seen ∧ rankAt state identity = some rank := by simpa [unseenAt] using selected
  have small := rankAt_bound state valid identity rank included.2
  omega

/-- Pointwise inclusion compares actual counts even when the issued ranges differ. -/
theorem count_mono (before after : State Symbol Guard) (beforeValid : Cache.Valid before.nodes)
    (afterValid : Cache.Valid after.nodes) (oldSeen newSeen : List Nat) (rank : Nat)
    (included : ∀ identity, unseenAt after newSeen rank identity = true → unseenAt before oldSeen rank identity = true) :
    count after newSeen rank ≤ count before oldSeen rank := by
  let large := max before.nodes.next after.nodes.next
  rw [← count_extend before beforeValid oldSeen rank large (Nat.le_max_left _ _),
    ← count_extend after afterValid newSeen rank large (Nat.le_max_right _ _)]
  exact List.countP_mono_left (fun identity _ selected => included identity selected)

/-- Removing one selected list member makes a pointwise smaller Boolean count strict. -/
theorem countP_strict (values : List Nat) (before after : Nat → Bool)
    (included : ∀ identity ∈ values, after identity = true → before identity = true)
    (identity : Nat) (member : identity ∈ values) (selected : before identity = true) (removed : after identity = false) :
    values.countP after < values.countP before := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      have tailMono := List.countP_mono_left (fun identity member selected => included identity (List.mem_cons_of_mem _ member) selected)
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.countP_cons, selected, removed, Bool.false_eq_true, ↓reduceIte] at *
        omega
      · have strict := ih (fun identity member selected => included identity (List.mem_cons_of_mem _ member) selected) member
        have firstMono := included first List.mem_cons_self
        cases a : before first <;> cases b : after first <;> simp_all <;> omega

/-- Pointwise inclusion with one removed canonical identity strictly decreases the actual degree count. -/
theorem count_strict (before after : State Symbol Guard) (beforeValid : Cache.Valid before.nodes)
    (afterValid : Cache.Valid after.nodes) (oldSeen newSeen : List Nat) (rank identity : Nat)
    (included : ∀ index, unseenAt after newSeen rank index = true → unseenAt before oldSeen rank index = true)
    (selected : unseenAt before oldSeen rank identity = true) (removed : unseenAt after newSeen rank identity = false) :
    count after newSeen rank < count before oldSeen rank := by
  let large := max before.nodes.next after.nodes.next
  rw [← count_extend before beforeValid oldSeen rank large (Nat.le_max_left _ _),
    ← count_extend after afterValid newSeen rank large (Nat.le_max_right _ _)]
  have selectedFacts : identity ∉ oldSeen ∧ rankAt before identity = some rank := by simpa [unseenAt] using selected
  have bound := rankAt_bound before beforeValid identity rank selectedFacts.2
  exact countP_strict (List.range large) _ _ (fun identity _ selected => included identity selected)
    identity (List.mem_range.mpr (by omega)) selected removed

/-- Recording another visited identity cannot increase any actual degree count. -/
theorem count_visit (state : State Symbol Guard) (valid : Cache.Valid state.nodes) (seen : List Nat)
    (identity rank : Nat) : count state (identity :: seen) rank ≤ count state seen rank := by
  apply count_mono state state valid valid seen (identity :: seen) rank
  intro index selected
  have facts : index ∉ identity :: seen ∧ rankAt state index = some rank := by simpa [unseenAt] using selected
  simp only [unseenAt, decide_eq_true_eq]
  exact ⟨fun member => facts.1 (List.mem_cons_of_mem _ member), facts.2⟩

/-- Each later canonical degree is an exact earlier degree or is below the allocation bound. -/
theorem rankAt_old_or_lower (before after : State Symbol Guard) (beforeCoherent : Coherent before)
    (afterCoherent : Coherent after) (bound identity rank : Nat) (lower : Lower before bound after)
    (found : rankAt after identity = some rank) : rankAt before identity = some rank ∨ rank < bound := by
  obtain ⟨entry, body, depth, ordinary, same, present, exactRank⟩ := (rankAt_spec after afterCoherent identity rank).mp found
  rcases lower entry.key entry body depth ordinary present with old | small
  · exact Or.inl (by simpa only [same, exactRank] using rankAt_record before beforeCoherent entry body depth ordinary old)
  · exact Or.inr (by omega)

/-- Visiting an unfolding cannot increase any degree at or above its old body depth. -/
theorem count_after_le (before after : State Symbol Guard) (beforeCoherent : Coherent before)
    (afterCoherent : Coherent after) (seen : List Nat) (identity bound rank : Nat)
    (lower : Lower before bound after) (above : bound ≤ rank) :
    count after (identity :: seen) rank ≤ count before seen rank := by
  apply count_mono before after beforeCoherent.valid.2 afterCoherent.valid.2 seen (identity :: seen) rank
  intro index selected
  have selectedFacts : index ∉ identity :: seen ∧ rankAt after index = some rank := by simpa [unseenAt] using selected
  have old : rankAt before index = some rank := by
    rcases rankAt_old_or_lower before after beforeCoherent afterCoherent bound index rank lower selectedFacts.2 with old | small
    · exact old
    · omega
  simp only [unseenAt, decide_eq_true_eq]
  exact ⟨fun member => selectedFacts.1 (List.mem_cons_of_mem _ member), old⟩

/-- An unseen canonical Mu consumes its own degree even when the cache adds lower-degree records. -/
theorem count_after_lt (before after : State Symbol Guard) (beforeCoherent : Coherent before)
    (afterCoherent : Coherent after) (seen : List Nat) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : before.nodeRecords entry.key = some (.mu entry body depth ordinary))
    (unseen : entry.identity ∉ seen) (lower : Lower before (valueDepth body) after) :
    count after (entry.identity :: seen) (valueDepth body) < count before seen (valueDepth body) := by
  apply count_strict before after beforeCoherent.valid.2 afterCoherent.valid.2 seen (entry.identity :: seen)
    (valueDepth body) entry.identity
  · intro index selected
    have selectedFacts : index ∉ entry.identity :: seen ∧ rankAt after index = some (valueDepth body) := by
      simpa [unseenAt] using selected
    have old : rankAt before index = some (valueDepth body) := by
      rcases rankAt_old_or_lower before after beforeCoherent afterCoherent (valueDepth body) index
        (valueDepth body) lower selectedFacts.2 with old | small
      · exact old
      · omega
    simp only [unseenAt, decide_eq_true_eq]
    exact ⟨fun member => selectedFacts.1 (List.mem_cons_of_mem _ member), old⟩
  · simp only [unseenAt, decide_eq_true_eq]
    exact ⟨unseen, rankAt_record before beforeCoherent entry body depth ordinary present⟩
  · simp [unseenAt]

/-- The actual finite degree vector strictly decreases when an unseen Mu adds only lower-depth records. -/
theorem counts_decrease (before after : State Symbol Guard) (beforeCoherent : Coherent before)
    (afterCoherent : Coherent after) (limit : Nat) (bounded : Bounded before limit)
    (seen : List Nat) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : before.nodeRecords entry.key = some (.mu entry body depth ordinary))
    (unseen : entry.identity ∉ seen) (lower : Lower before (valueDepth body) after) :
    HeightOrder.Below limit (count after (entry.identity :: seen)) (count before seen) := by
  apply HeightOrder.below_of_decrease limit _ _ (valueDepth body)
    (bounded entry.key entry body depth ordinary present)
    (count_after_lt before after beforeCoherent afterCoherent seen entry body depth ordinary present unseen lower)
  intro rank above inside
  exact count_after_le before after beforeCoherent afterCoherent seen entry.identity (valueDepth body) rank lower (by omega)

end MicroCFTA.InternedMuDepthInventory
