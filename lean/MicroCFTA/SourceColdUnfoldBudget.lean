import MicroCFTA.SourceColdSharedRows

/-!
# A finite budget for unfinished cold Mu unfoldings

The initial complete-record inventory contains every later Mu. Completed
unfoldings replay without effects after cache growth. Each first unfolding
therefore reduces a finite budget if it changes the cache.
-/
namespace MicroCFTA.SourceColdUnfoldBudget
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedFacts InternedNestedProvenance InternedShallowHeap MergedPhysicalWarmup

/-- A stored unfolding is settled when it completes without a cache effect. -/
def Settled [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ result, InternedStoredSubstitution.unfold value state = .done result state

/-- Later cache growth retains each settled exact source unfolding. -/
theorem Settled.grows [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows before after) (value : Value Symbol Guard) (settled : Settled before value) :
    Settled after value := by
  obtain ⟨result, done⟩ := settled
  exact ⟨result, unfold_replay value before after result before valid done growth⟩

/-- Every completed source unfolding is settled in its actual returned cache. -/
theorem settled_after [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (value result : Value Symbol Guard)
    (done : InternedStoredSubstitution.unfold value before = .done result after) : Settled after value :=
  ⟨result, unfold_replay value before after result after valid done (grows_refl _)⟩

noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Count the unfinished source unfoldings in a fixed finite physical inventory. -/
def remaining [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) : List (Value Symbol Guard) → Nat
  | [] => 0
  | value :: rest => (if Settled state value then 0 else 1) + remaining state rest

/-- Source cache growth cannot increase the number of unfinished unfoldings. -/
theorem remaining_mono [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows before after) (inventory : List (Value Symbol Guard)) :
    remaining after inventory ≤ remaining before inventory := by
  induction inventory with
  | nil => exact Nat.le_refl _
  | cons value rest ih =>
      by_cases old : Settled before value
      · have later := old.grows before after valid growth value
        simpa only [remaining, ite_eq_left old, ite_eq_left later, Nat.zero_add] using ih
      · by_cases later : Settled after value <;> simp only [remaining, old, later, ite_true, ite_false] <;> omega

/-- Settling any unfinished inventory member strictly decreases the finite budget. -/
theorem remaining_lt [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows before after) (inventory : List (Value Symbol Guard))
    (value : Value Symbol Guard) (member : value ∈ inventory) (old : ¬ Settled before value) (later : Settled after value) :
    remaining after inventory < remaining before inventory := by
  induction inventory with
  | nil => cases member
  | cons first rest ih =>
      have monotone := remaining_mono before after valid growth rest
      rcases List.mem_cons.mp member with rfl | member
      · simp only [remaining, ite_eq_right old, ite_eq_left later]
        omega
      · have shorter := ih member
        by_cases firstOld : Settled before first
        · have firstLater := firstOld.grows before after valid growth first
          simpa only [remaining, ite_eq_left firstOld, ite_eq_left firstLater, Nat.zero_add] using shorter
        · by_cases firstLater : Settled after first <;>
            simp only [remaining, firstOld, firstLater, ite_true, ite_false] <;> omega

/-- The fixed initial inventory contains every actual current complete Mu record. -/
def Covers (state : State Symbol Guard) (inventory : List (Value Symbol Guard)) : Prop :=
  ∀ entry body depth ordinary, Available state (.mu entry body depth ordinary) →
    Value.mu entry body depth ordinary ∈ inventory

/-- The actual finite issued-record inventory supplies the initial Mu budget. -/
theorem initial_covers (state : State Symbol Guard) (facts : Facts state) : Covers state (nodeInventory state) := by
  intro entry body depth ordinary available
  exact inventory_complete state facts.coherent entry.key _ (available.resident entry rfl)

/-- Source reads that add no Mu preserve the initial finite inventory's coverage. -/
theorem Covers.preserve (before after : State Symbol Guard) (facts : Facts before)
    (inventory : List (Value Symbol Guard)) (covered : Covers before inventory) (unchanged : NoNewMu before after) :
    Covers after inventory := by
  intro entry body depth ordinary available
  exact covered entry body depth ordinary
    (facts.cached.nodes entry.key _ (unchanged entry.key entry body depth ordinary (available.resident entry rfl)))

/-- An unfolding with unchanged finite budget has no physical cache effect. -/
theorem unfold_unchanged [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (facts : Facts before) (inventory : List (Value Symbol Guard))
    (covered : Covers before inventory) (value : Value Symbol Guard) (available : Available before value)
    (result : Value Symbol Guard) (done : InternedStoredSubstitution.unfold value before = .done result after)
    (sameBudget : remaining after inventory = remaining before inventory) : after = before := by
  cases value with
  | empty | reference | node | union => exact (Outcome.done.inj done).2.symm
  | mu entry body depth ordinary =>
      by_cases settled : Settled before (.mu entry body depth ordinary)
      · obtain ⟨previous, previousDone⟩ := settled
        exact (Outcome.done.inj (done.symm.trans previousDone)).2
      · have checked := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) before facts available
        have growth : Grows before after := by simpa only [done, Outcome.state] using checked.growth
        have strict := remaining_lt before after facts.coherent.valid growth inventory (.mu entry body depth ordinary)
          (covered entry body depth ordinary available) settled
          (settled_after before after facts.coherent.valid _ result done)
        omega

end
end MicroCFTA.SourceColdUnfoldBudget
