import MicroCFTA.MergedPhysicalWarmup

/-!
# Stabilization of one actual cold unfolding schedule

Every query consumes the cache returned by the preceding query. The
proof uses no reordered allocation history. Each repeated Mu unfolds by
replaying its own earlier completed call. Only an initial complete Mu's
first encounter can change the cache.
-/
namespace MicroCFTA.MergedColdUnfolding
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedShallowHeap MergedPhysicalWarmup
open InternedBinderProtocol (NodeKey)

/-- One chronological source schedule records the actual input, result, and cache of each completed query. -/
structure Schedule (Symbol Guard : Type) [DecidableEq (EdgeKey Symbol Guard)] where
  state : Nat → State Symbol Guard
  input : Nat → Value Symbol Guard
  result : Nat → Value Symbol Guard
  available : ∀ index, Available (state index) (input index)
  done : ∀ index, InternedStoredSubstitution.unfold (input index) (state index) =
    .done (result index) (state (index + 1))

/-- The actual sequential trace retains facts, preparation, growth, and its initial Mu payloads. -/
theorem invariants [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (index : Nat) :
    Facts (schedule.state index) ∧ Prepared (schedule.state index) ∧
      Grows (schedule.state 0) (schedule.state index) ∧ NoNewMu (schedule.state 0) (schedule.state index) := by
  induction index with
  | zero => exact ⟨facts, prepared, grows_refl _, noNewMu_refl _⟩
  | succ index ih =>
      have verified := InternedStoredSubstitution.unfold_verified (schedule.input index) (schedule.state index) ih.1
        (schedule.available index)
      have afterFacts : Facts (schedule.state (index + 1)) := by simpa only [schedule.done index, Outcome.state] using verified.facts
      have growth : Grows (schedule.state index) (schedule.state (index + 1)) := by simpa only [schedule.done index, Outcome.state] using verified.growth
      have unchanged : NoNewMu (schedule.state index) (schedule.state (index + 1)) := by
        simpa only [schedule.done index, Outcome.state] using
          unfold_noNewMu (schedule.input index) (schedule.state index) ih.2.1 (schedule.available index)
      exact ⟨afterFacts, ih.2.1.preserve unchanged, grows_trans ih.2.2.1 growth, noNewMu_trans ih.2.2.2 unchanged⟩

/-- Any earlier actual cache extends along this same sequential trace. -/
theorem growth [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (first last : Nat) (ordered : first ≤ last) :
    Grows (schedule.state first) (schedule.state last) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
  clear ordered
  induction extra with
  | zero => simpa using grows_refl (schedule.state first)
  | succ extra ih =>
      let last := first + extra
      have verified := InternedStoredSubstitution.unfold_verified (schedule.input last) (schedule.state last)
        (invariants schedule facts prepared last).1 (schedule.available last)
      have next : Grows (schedule.state last) (schedule.state (last + 1)) := by
        simpa only [schedule.done last, Outcome.state] using verified.growth
      simpa only [last, Nat.add_succ] using grows_trans ih next

/-- A value retains availability in each later cache of the actual trace. -/
theorem available_later [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (first last : Nat) (ordered : first ≤ last) (value : Value Symbol Guard)
    (available : Available (schedule.state first) value) : Available (schedule.state last) value := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
  clear ordered
  induction extra with
  | zero => simpa using available
  | succ extra ih =>
      let last := first + extra
      have verified := InternedStoredSubstitution.unfold_verified (schedule.input last) (schedule.state last)
        (invariants schedule facts prepared last).1 (schedule.available last)
      simpa only [schedule.done last, Outcome.state, last, Nat.add_succ] using verified.available value ih

/-- A repeated actual input returns its earlier complete result and allocates nothing. -/
theorem repeated [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (first last : Nat) (earlier : first < last) (same : schedule.input first = schedule.input last) :
    schedule.result last = schedule.result first ∧ schedule.state (last + 1) = schedule.state last := by
  have replay := unfold_replay (schedule.input first) (schedule.state first) (schedule.state last)
    (schedule.result first) (schedule.state (first + 1))
    (invariants schedule facts prepared first).1.coherent.valid (schedule.done first)
    (growth schedule facts prepared (first + 1) last earlier)
  rw [same] at replay
  exact Outcome.done.inj ((schedule.done last).symm.trans replay)

/-- Equal inputs anywhere in one actual trace have equal completed results. -/
theorem same_result [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (first last : Nat) (same : schedule.input first = schedule.input last) : schedule.result first = schedule.result last := by
  rcases Nat.lt_trichotomy first last with earlier | equal | later
  · exact (repeated schedule facts prepared first last earlier same).1.symm
  · rw [equal]
  · exact (repeated schedule facts prepared last first later same.symm).1

/-- Every Mu queried by the cold schedule was already a complete original cache record. -/
theorem mu_origin [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (index : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (shape : schedule.input index = .mu entry body depth ordinary) :
    schedule.input index ∈ nodeInventory (schedule.state 0) := by
  have available : Available (schedule.state index) (.mu entry body depth ordinary) := shape ▸ schedule.available index
  have original := (invariants schedule facts prepared index).2.2.2 entry.key entry body depth ordinary (available.resident entry rfl)
  rw [shape]
  exact inventory_complete _ facts.coherent entry.key _ original

/-- An allocating query must be an initial Mu record. -/
theorem changed_origin [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (index : Nat)
    (changed : schedule.state (index + 1) ≠ schedule.state index) :
    schedule.input index ∈ nodeInventory (schedule.state 0) := by
  cases shape : schedule.input index with
  | mu entry body depth ordinary => simpa only [shape] using mu_origin schedule facts prepared index entry body depth ordinary shape
  | empty | reference | node | union =>
      have done := schedule.done index
      simp only [shape, InternedStoredSubstitution.unfold, Outcome.done.injEq] at done
      exact False.elim (changed done.2.symm)

/-- Every changed cache comes from an input that has not been queried earlier. -/
theorem changed_first [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (index : Nat)
    (changed : schedule.state (index + 1) ≠ schedule.state index) (earlier : Nat) (before : earlier < index) :
    schedule.input earlier ≠ schedule.input index := by
  intro same
  exact changed (repeated schedule facts prepared earlier index before same).2

/-- Distinct cache-changing calls cannot have the same actual input. -/
theorem changed_injective [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (first last : Nat) (firstChanged : schedule.state (first + 1) ≠ schedule.state first)
    (lastChanged : schedule.state (last + 1) ≠ schedule.state last)
    (same : schedule.input first = schedule.input last) : first = last := by
  rcases Nat.lt_trichotomy first last with earlier | equal | later
  · exact False.elim (changed_first schedule facts prepared last lastChanged first earlier same)
  · exact equal
  · exact False.elim (changed_first schedule facts prepared first firstChanged last later same.symm)

/-- The initial issued counter bounds all cache-changing calls in any finite part of the actual trace. -/
theorem changes_bounded [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (indices : List Nat) (unique : indices.Nodup)
    (changed : ∀ index ∈ indices, schedule.state (index + 1) ≠ schedule.state index) :
    indices.length ≤ (nodeInventory (schedule.state 0)).length ∧
      indices.length ≤ (schedule.state 0).nodes.next := by
  have mapped : (indices.map schedule.input).Nodup := by
    induction indices with
    | nil => simp
    | cons first rest ih =>
        have parts := List.nodup_cons.mp unique
        apply List.nodup_cons.mpr
        constructor
        · intro member
          obtain ⟨last, included, same⟩ := List.mem_map.mp member
          have equal := changed_injective schedule facts prepared first last
            (changed first List.mem_cons_self) (changed last (List.mem_cons_of_mem _ included)) same.symm
          exact parts.1 (equal ▸ included)
        · exact ih parts.2 (fun index member => changed index (List.mem_cons_of_mem _ member))
  have covered : indices.map schedule.input ⊆ nodeInventory (schedule.state 0) := by
    intro value member
    obtain ⟨index, included, rfl⟩ := List.mem_map.mp member
    exact changed_origin schedule facts prepared index (changed index included)
  have bounded : indices.length ≤ (nodeInventory (schedule.state 0)).length := by
    simpa only [List.length_map] using mapped.length_le_of_subset covered
  exact ⟨bounded, Nat.le_trans bounded (node_inventory_bound _)⟩

/-- A finite input list has a finite prefix containing an occurrence of every member that is ever queried. -/
theorem finite_seen (values : List Item) (query : Nat → Item) :
    ∃ bound, ∀ value ∈ values, (∃ index, query index = value) → ∃ index, index < bound ∧ query index = value := by
  classical
  induction values with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
      obtain ⟨tailBound, covered⟩ := ih
      by_cases seen : ∃ index, query index = first
      · obtain ⟨index, equal⟩ := seen
        refine ⟨max (index + 1) tailBound, ?_⟩
        intro value member appears
        rcases List.mem_cons.mp member with same | member
        · exact ⟨index, Nat.lt_of_lt_of_le (Nat.lt_succ_self index) (Nat.le_max_left _ _), equal.trans same.symm⟩
        · obtain ⟨position, before, found⟩ := covered value member appears
          exact ⟨position, Nat.lt_of_lt_of_le before (Nat.le_max_right _ _), found⟩
      · refine ⟨tailBound, ?_⟩
        intro value member appears
        rcases List.mem_cons.mp member with same | member
        · exact False.elim (seen (same ▸ appears))
        · exact covered value member appears

/-- Every actual cold schedule eventually has a constant cache and only finitely many recursive results. -/
theorem stabilizes [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) :
    ∃ bound, (∀ index, bound ≤ index → schedule.state index = schedule.state bound) ∧
      ∀ index entry body depth ordinary, schedule.input index = .mu entry body depth ordinary →
        schedule.result index ∈ (List.range bound).map schedule.result := by
  obtain ⟨bound, covered⟩ := finite_seen (nodeInventory (schedule.state 0)) schedule.input
  have fixed : ∀ index, bound ≤ index → schedule.state (index + 1) = schedule.state index := by
    intro index after
    by_cases changed : schedule.state (index + 1) = schedule.state index
    · exact changed
    exfalso
    obtain ⟨earlier, before, same⟩ := covered (schedule.input index)
      (changed_origin schedule facts prepared index changed) ⟨index, rfl⟩
    exact changed (repeated schedule facts prepared earlier index (by omega) same).2
  refine ⟨bound, ?_, ?_⟩
  · intro index after
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
    clear after
    induction extra with
    | zero => simp
    | succ extra ih =>
        simpa only [Nat.add_succ] using (fixed (bound + extra) (by omega)).trans ih
  · intro index entry body depth ordinary shape
    obtain ⟨earlier, before, same⟩ := covered (schedule.input index)
      (mu_origin schedule facts prepared index entry body depth ordinary shape) ⟨index, rfl⟩
    exact List.mem_map.mpr ⟨earlier, List.mem_range.mpr before, same_result schedule facts prepared earlier index same⟩

end MicroCFTA.MergedColdUnfolding
