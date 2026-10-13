import MicroCFTA.MergedColdUnfolding
import MicroCFTA.MergedPhysicalComparison

/-!
# Finite physical inventories for actual cold comparison requests

Each request comes from a finite root list, an earlier retained child,
or an earlier completed result. One actual trace supplies its own stable
cache. The proof compares no alternative allocation orders.
-/
namespace MicroCFTA.MergedColdInventory
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedPhysicalComparison MergedColdUnfolding

/-- Source reads can request roots, retained children, or prior unfolding results. -/
def Generated [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (roots : List (Value Symbol Guard)) : Prop :=
  ∀ index, schedule.input index ∈ roots ∨
    (∃ earlier, earlier < index ∧ schedule.input index ∈ children (schedule.input earlier)) ∨
    (∃ earlier, earlier < index ∧ schedule.input index = schedule.result earlier)

/-- Earlier and later available values are available at the stable cache of the same trace. -/
theorem available_stable [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (bound : Nat)
    (stable : ∀ index, bound ≤ index → schedule.state index = schedule.state bound)
    (index : Nat) (value : Value Symbol Guard) (available : Available (schedule.state index) value) :
    Available (schedule.state bound) value := by
  by_cases before : index ≤ bound
  · exact available_later schedule facts prepared index bound before value available
  · simpa only [stable index (by omega)] using available

/-- Every completed query replays exactly in its own trace's stable cache. -/
theorem replay_stable [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (bound : Nat)
    (stable : ∀ index, bound ≤ index → schedule.state index = schedule.state bound) (index : Nat) :
    InternedStoredSubstitution.unfold (schedule.input index) (schedule.state bound) =
      .done (schedule.result index) (schedule.state bound) := by
  apply unfold_replay (schedule.input index) (schedule.state index) (schedule.state bound)
    (schedule.result index) (schedule.state (index + 1))
    (invariants schedule facts prepared index).1.coherent.valid (schedule.done index)
  by_cases before : index + 1 ≤ bound
  · exact growth schedule facts prepared _ _ before
  · rw [stable (index + 1) (by omega)]
    exact grows_refl _

/-- Every actual result retains source availability at the stable cache. -/
theorem result_stable [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0)) (bound : Nat)
    (stable : ∀ index, bound ≤ index → schedule.state index = schedule.state bound) (index : Nat) :
    Available (schedule.state bound) (schedule.result index) := by
  have verified := InternedStoredSubstitution.unfold_verified (schedule.input index) (schedule.state index)
    (invariants schedule facts prepared index).1 (schedule.available index)
  exact available_stable schedule facts prepared bound stable (index + 1) _
    (verified.result _ _ (schedule.done index))

/-- The actual source schedule derives its own finite inventory without an eager warmup. -/
theorem finite_inventory [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (roots : List (Value Symbol Guard)) (inputs : Values (schedule.state 0) roots)
    (generated : Generated schedule roots) :
    ∃ bound, let outputs := (List.range bound).map schedule.result
      (∀ index, bound ≤ index → schedule.state index = schedule.state bound) ∧
      Facts (schedule.state bound) ∧ Values (schedule.state bound) roots ∧ Values (schedule.state bound) outputs ∧
      (∀ index, schedule.input index ∈ inventory (schedule.state bound) roots outputs) ∧
      (∀ index, schedule.result index ∈ inventory (schedule.state bound) roots outputs) ∧
      ∀ index, InternedStoredSubstitution.unfold (schedule.input index) (schedule.state bound) =
        .done (schedule.result index) (schedule.state bound) := by
  obtain ⟨bound, stable, recursive⟩ := stabilizes schedule facts prepared
  let outputs := (List.range bound).map schedule.result
  let domain := inventory (schedule.state bound) roots outputs
  have finalFacts := (invariants schedule facts prepared bound).1
  have finalInputs : Values (schedule.state bound) roots := by
    intro value member
    exact available_later schedule facts prepared 0 bound (Nat.zero_le _) value (inputs value member)
  have results : Values (schedule.state bound) outputs := by
    intro value member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact result_stable schedule facts prepared bound stable index
  have covered : ∀ index, schedule.input index ∈ domain := by
    intro index
    induction index using Nat.strongRecOn with
    | ind index ih =>
        rcases generated index with root | ⟨earlier, before, child⟩ | ⟨earlier, before, same⟩
        · simp [domain, inventory, root]
        · exact child_member (schedule.state bound) finalFacts roots outputs _ _
            (available_stable schedule facts prepared bound stable earlier _ (schedule.available earlier)) child
        · rw [same]
          cases shape : schedule.input earlier with
          | mu entry body depth ordinary =>
              have retained := recursive earlier entry body depth ordinary shape
              simp [domain, inventory, outputs, retained]
          | empty | reference | node | union =>
              have done := schedule.done earlier
              simp only [shape, InternedStoredSubstitution.unfold, Outcome.done.injEq] at done
              rw [← done.1, ← shape]
              exact ih earlier before
  refine ⟨bound, stable, finalFacts, finalInputs, results, covered, ?_, ?_⟩
  · intro index
    cases shape : schedule.input index with
    | mu entry body depth ordinary =>
        have retained := recursive index entry body depth ordinary shape
        simp [inventory, retained]
    | empty | reference | node | union =>
        have done := schedule.done index
        simp only [shape, InternedStoredSubstitution.unfold, Outcome.done.injEq] at done
        rw [← done.1, ← shape]
        exact covered index
  · exact replay_stable schedule facts prepared bound stable

/-- A sequence in a finite inventory repeats within one more than its length. -/
theorem finite_repetition (values : List Item) (query : Nat → Item)
    (covered : ∀ index, query index ∈ values) :
    ∃ earlier later, earlier < later ∧ later ≤ values.length ∧ query earlier = query later := by
  classical
  by_cases repeats : ∃ earlier later, earlier < later ∧ later ≤ values.length ∧ query earlier = query later
  · exact repeats
  exfalso
  have unique : ((List.range (values.length + 1)).map query).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.pairwise_lt_range)
    intro first last _ lastIn earlier same
    exact repeats ⟨first, last, earlier, by have bound := List.mem_range.mp lastIn; omega, same⟩
  have bounded := unique.length_le_of_subset (l₂ := values) (by
    intro value member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact covered index)
  simp only [List.length_map, List.length_range] at bounded
  omega

/-- Pairs in a finite physical state inventory repeat within its square. -/
theorem finite_pair_repetition (values : List Item) (wide narrow : Nat → Item)
    (wideIn : ∀ index, wide index ∈ values) (narrowIn : ∀ index, narrow index ∈ values) :
    ∃ earlier later, earlier < later ∧ later ≤ values.length * values.length ∧
      (wide earlier, narrow earlier) = (wide later, narrow later) := by
  let pairs := values.flatMap fun first => values.map (first, ·)
  have count : pairs.length = values.length * values.length := by
    simp only [pairs, List.length_flatMap, List.length_map]
    have repeated (items : List Item) (amount : Nat) : (items.map (fun _ => amount)).sum = items.length * amount := by
      induction items with
      | nil => simp
      | cons first rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
    exact repeated values values.length
  obtain ⟨first, last, earlier, bounded, same⟩ := finite_repetition pairs (fun index => (wide index, narrow index)) (by
    intro index
    exact List.mem_flatMap.mpr ⟨wide index, wideIn index, List.mem_map.mpr ⟨narrow index, narrowIn index, rfl⟩⟩)
  exact ⟨first, last, earlier, count ▸ bounded, same⟩

/-- An infinite cold comparison descent must repeat an ancestor pair from its own derived inventory. -/
theorem pair_repetition [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (roots : List (Value Symbol Guard)) (inputs : Values (schedule.state 0) roots)
    (generated : Generated schedule roots) :
    ∃ bound, ∀ wide narrow : Nat → Nat, ∃ earlier later,
      earlier < later ∧
      later ≤ (inventory (schedule.state bound) roots ((List.range bound).map schedule.result)).length *
        (inventory (schedule.state bound) roots ((List.range bound).map schedule.result)).length ∧
      (schedule.input (wide earlier), schedule.input (narrow earlier)) =
        (schedule.input (wide later), schedule.input (narrow later)) := by
  obtain ⟨bound, _, _, _, _, covered, _, _⟩ := finite_inventory schedule facts prepared roots inputs generated
  refine ⟨bound, ?_⟩
  intro wide narrow
  exact finite_pair_repetition _ (fun index => schedule.input (wide index))
    (fun index => schedule.input (narrow index)) (fun index => covered (wide index)) (fun index => covered (narrow index))

/-- The source's ancestor-pair test excludes an infinite fresh-pair cold descent. -/
theorem no_fresh_pairs [DecidableEq (EdgeKey Symbol Guard)] (schedule : Schedule Symbol Guard)
    (facts : Facts (schedule.state 0)) (prepared : Prepared (schedule.state 0))
    (roots : List (Value Symbol Guard)) (inputs : Values (schedule.state 0) roots)
    (generated : Generated schedule roots) (wide narrow : Nat → Nat)
    (fresh : ∀ earlier later, earlier < later →
      (schedule.input (wide earlier), schedule.input (narrow earlier)) ≠
        (schedule.input (wide later), schedule.input (narrow later))) : False := by
  obtain ⟨_, repeats⟩ := pair_repetition schedule facts prepared roots inputs generated
  obtain ⟨earlier, later, before, _, same⟩ := repeats wide narrow
  exact fresh earlier later before same

end MicroCFTA.MergedColdInventory
