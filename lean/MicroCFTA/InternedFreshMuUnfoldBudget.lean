import MicroCFTA.MergedFreshOrdinaryColdTermination

/-!
# Dynamic counts of unfinished repaired Mu unfoldings

Completed unfoldings replay without allocation after cache growth. Count
unfinished canonical records at each open-body degree. An actual unfolding
either retains its exact cache or strictly reduces this finite vector.
-/
namespace MicroCFTA.InternedFreshMuUnfoldBudget
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedStoredPlanBinderDepth InternedMuDepthInventory
open InternedStoredPlanBinderDepthProgress (Lower)
open InternedBinderProtocol (NodeKey)
open InternedNestedConstruction (Outcome)

/-- A repaired unfolding is settled when it completes with no cache effect. -/
def Settled [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ result, InternedFreshOrdinaryStoredSubstitution.unfold value state = .done result state

/-- Actual allocation-free replay retains settled calls after cache growth. -/
theorem Settled.grows [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows before after) (value : Value Symbol Guard) (settled : Settled before value) :
    Settled after value := by
  obtain ⟨result, done⟩ := settled
  exact ⟨result, InternedFreshOrdinaryStoredSubstitution.unfold_replay value before after result before valid done growth⟩

/-- Every completed repaired unfolding is settled in its exact returned cache. -/
theorem settled_after [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (value result : Value Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after) : Settled after value :=
  ⟨result, InternedFreshOrdinaryStoredSubstitution.unfold_replay value before after result after valid done (grows_refl _)⟩

noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Select an unfinished actual Mu only at its own canonical identity and body degree. -/
def unfinishedAt [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (degree identity : Nat) : Bool :=
  decide (∃ entry body depth ordinary, entry.identity = identity ∧
    state.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧ valueDepth body = degree ∧
    ¬ Settled state (.mu entry body depth ordinary))

/-- Count unfinished canonical Mu records in the actual finite issued range. -/
def count [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (degree : Nat) : Nat :=
  (List.range state.nodes.next).countP (unfinishedAt state degree)

/-- A completed read either reduces its unfinished degree vector or retains its exact cache. -/
def Progress [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (before after : State Symbol Guard) : Prop :=
  HeightOrder.VectorBelow limit (fun index => count after index) (fun index => count before index) ∨ after = before

/-- Cache equality and strict degree progress compose through actual sequential effects. -/
theorem Progress.trans [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (before middle after : State Symbol Guard)
    (one : Progress limit before middle) (two : Progress limit middle after) : Progress limit before after := by
  rcases one with one | rfl
  · rcases two with two | rfl
    · exact Or.inl (HeightOrder.below_trans limit _ _ _ two one)
    · exact Or.inl one
  · exact two

/-- Every selected unfinished record has its actual canonical rank lookup. -/
theorem unfinished_rank [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (coherent : Coherent state)
    (degree identity : Nat) (selected : unfinishedAt state degree identity = true) : rankAt state identity = some degree := by
  obtain ⟨entry, body, depth, ordinary, same, present, exactRank, _⟩ := of_decide_eq_true selected
  simpa only [same, exactRank] using rankAt_record state coherent entry body depth ordinary present

/-- Any larger issued range gives the same count of actual canonical records. -/
theorem count_extend [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (coherent : Coherent state)
    (degree large : Nat) (inside : state.nodes.next ≤ large) :
    (List.range large).countP (unfinishedAt state degree) = count state degree := by
  apply countP_extend _ _ large inside
  intro identity outside
  apply Bool.eq_false_iff.mpr
  intro selected
  have bound := rankAt_bound state coherent.valid.2 identity degree (unfinished_rank state coherent degree identity selected)
  omega

/-- Pointwise inclusion compares counts even when the actual issued ranges differ. -/
theorem count_mono [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (beforeCoherent : Coherent before) (afterCoherent : Coherent after) (degree : Nat)
    (included : ∀ identity, unfinishedAt after degree identity = true → unfinishedAt before degree identity = true) :
    count after degree ≤ count before degree := by
  let large := max before.nodes.next after.nodes.next
  rw [← count_extend before beforeCoherent degree large (Nat.le_max_left _ _),
    ← count_extend after afterCoherent degree large (Nat.le_max_right _ _)]
  exact List.countP_mono_left (fun identity _ selected => included identity selected)

/-- Lower-degree allocation and replay prevent any new unfinished record at higher degrees. -/
theorem unfinished_old [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (beforeCoherent : Coherent before) (growth : Grows before after) (bound degree identity : Nat)
    (lower : Lower before bound after) (above : bound ≤ degree)
    (selected : unfinishedAt after degree identity = true) : unfinishedAt before degree identity = true := by
  obtain ⟨entry, body, depth, ordinary, same, present, exactRank, unsettled⟩ := of_decide_eq_true selected
  have old : before.nodeRecords entry.key = some (.mu entry body depth ordinary) := by
    rcases lower entry.key entry body depth ordinary present with old | small
    · exact old
    · omega
  apply decide_eq_true
  exact ⟨entry, body, depth, ordinary, same, old, exactRank,
    fun settled => unsettled (Settled.grows before after beforeCoherent.valid growth _ settled)⟩

/-- Actual lower-degree allocation cannot increase the unfinished counts at or above its bound. -/
theorem count_after_le [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (beforeCoherent : Coherent before) (afterCoherent : Coherent after) (growth : Grows before after)
    (bound degree : Nat) (lower : Lower before bound after) (above : bound ≤ degree) :
    count after degree ≤ count before degree :=
  count_mono before after beforeCoherent afterCoherent degree
    (fun identity selected => unfinished_old before after beforeCoherent growth bound degree identity lower above selected)

/-- Settling the queried canonical Mu strictly consumes its own unfinished degree. -/
theorem count_after_lt [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (beforeCoherent : Coherent before) (afterCoherent : Coherent after) (growth : Grows before after)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : before.nodeRecords entry.key = some (.mu entry body depth ordinary))
    (unsettled : ¬ Settled before (.mu entry body depth ordinary))
    (settled : Settled after (.mu entry body depth ordinary)) (lower : Lower before (valueDepth body) after) :
    count after (valueDepth body) < count before (valueDepth body) := by
  let large := max before.nodes.next after.nodes.next
  rw [← count_extend before beforeCoherent (valueDepth body) large (Nat.le_max_left _ _),
    ← count_extend after afterCoherent (valueDepth body) large (Nat.le_max_right _ _)]
  apply countP_strict (List.range large) _ _
    (fun identity _ selected => unfinished_old before after beforeCoherent growth _ _ identity lower (Nat.le_refl _) selected)
    entry.identity
  · have bound := rankAt_bound before beforeCoherent.valid.2 entry.identity (valueDepth body)
      (rankAt_record before beforeCoherent entry body depth ordinary present)
    exact List.mem_range.mpr (by omega)
  · apply decide_eq_true
    exact ⟨entry, body, depth, ordinary, rfl, present, rfl, unsettled⟩
  · apply Bool.eq_false_iff.mpr
    intro selected
    obtain ⟨other, otherBody, otherDepth, otherOrdinary, same, otherPresent, _, otherUnsettled⟩ := of_decide_eq_true selected
    have ownPresent := growth.nodeRecords entry.key _ present
    have otherIssued := (afterCoherent.valid.2.2 other.key other
      (resident_entry after afterCoherent _ (stored_resident after afterCoherent other.key _ otherPresent) other rfl)).2
    have ownCanonical := afterCoherent.valid.2.2 entry.key entry
      (resident_entry after afterCoherent _ (stored_resident after afterCoherent entry.key _ ownPresent) entry rfl)
    have keyEqual : other.key = entry.key := by
      rw [same] at otherIssued
      exact Option.some.inj (otherIssued.symm.trans ownCanonical.2)
    rw [keyEqual, ownPresent] at otherPresent
    cases Option.some.inj otherPresent
    exact otherUnsettled settled

/-- One completed actual unfolding either keeps the exact cache or reduces the finite degree vector. -/
theorem unfold_progress [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (covered : Covered [] before) (heap : InternedOpenDepthReadback.Heap before) (bounded : Bounded before limit)
    (available : Available before value) (closed : value.free = []) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after) :
    Progress limit before after := by
  cases value with
  | empty | reference | node | union => exact Or.inr (Outcome.done.inj done).2.symm
  | mu entry body depth ordinary =>
      by_cases settled : Settled before (.mu entry body depth ordinary)
      · obtain ⟨previous, repeated⟩ := settled
        exact Or.inr (Outcome.done.inj (done.symm.trans repeated)).2
      · obtain ⟨actual, final, finished, afterContext, afterCached, _, _, growth, _⟩ :=
          InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
            before semantic.1 available semantic.2 covered
        obtain ⟨rfl, rfl⟩ := Outcome.done.inj (done.symm.trans finished)
        have lower : Lower before (valueDepth body) after := by
          simpa only [done, Outcome.state, bodyDepth] using InternedStoredPlanBinderDepthProgress.unfold_new_lower
            (.mu entry body depth ordinary) before semantic.1 semantic.2 heap available closed
        have present := available.resident entry rfl
        apply Or.inl
        apply HeightOrder.vector_decreases limit _ _ ⟨valueDepth body, bounded entry.key entry body depth ordinary present⟩
          (count_after_lt before after semantic.1.normal.facts.coherent afterContext.normal.facts.coherent growth
            entry body depth ordinary present settled (settled_after before after semantic.1.normal.facts.coherent.valid _ _ done) lower)
        intro degree above
        change valueDepth body < degree.val at above
        exact count_after_le before after semantic.1.normal.facts.coherent afterContext.normal.facts.coherent growth
          (valueDepth body) degree lower (by omega)

end
end MicroCFTA.InternedFreshMuUnfoldBudget
