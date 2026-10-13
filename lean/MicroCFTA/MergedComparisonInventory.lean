import MicroCFTA.MergedSubsumptionTermination

/-!
# Coverage search over a local physical inventory

The pair bound needs only the states reached by the current comparison.
Outgoing child closure supplies each recursive premise. No finite list of
every value of the ambient state type is required.
-/
namespace MicroCFTA.MergedComparisonInventory
open Language MergedAlternativesSubsumption

/-- Every outgoing comparison child stays inside the selected state domain. -/
def Closed (automaton : Automaton State Symbol) (domain : State → Prop) : Prop :=
  ∀ state, domain state → ∀ edge ∈ automaton state, ∀ child ∈ edge.children, domain child

/-- Child comparison depends only on pairs drawn from the two supplied lists. -/
theorem children_congr (first second : State → State → Bool) (wides narrows : List State)
    (same : ∀ wide ∈ wides, ∀ narrow ∈ narrows, first wide narrow = second wide narrow) :
    checkChildren first wides narrows = checkChildren second wides narrows := by
  induction wides generalizing narrows with
  | nil => cases narrows <;> rfl
  | cons wide wides ih =>
      cases narrows with
      | nil => rfl
      | cons narrow narrows =>
          rw [checkChildren, checkChildren, same wide (by simp) narrow (by simp)]
          rw [ih narrows (fun a ha b hb => same a (by simp [ha]) b (by simp [hb]))]

/-- A local pair inventory suffices once every recursive child stays in its domain. -/
theorem check_stable [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (unconstrained : Edge State Symbol → Bool)
    (domain : State → Prop) (closed : Closed automaton domain)
    (remaining above : List (State × State))
    (covered : ∀ first, domain first → ∀ second, domain second →
      (first, second) ∈ above ∨ (first, second) ∈ remaining)
    (fuel : Nat) (enough : remaining.length ≤ fuel) (wide narrow : State)
    (wideIn : domain wide) (narrowIn : domain narrow) :
    check automaton unconstrained fuel above wide narrow =
      check automaton unconstrained (fuel + 1) above wide narrow := by
  by_cases same : wide = narrow
  · cases fuel <;> simp [check, same]
  by_cases seen : (wide, narrow) ∈ above
  · cases fuel <;> simp [check, same, seen]
  have present := (covered wide wideIn narrow narrowIn).resolve_left seen
  have positive := List.length_pos_of_mem present
  cases fuel with
  | zero => omega
  | succ fuel =>
      have reduced : (remaining.erase (wide, narrow)).length ≤ fuel := by
        rw [List.length_erase_of_mem present]
        omega
      have retained : ∀ first, domain first → ∀ second, domain second →
          (first, second) ∈ (wide, narrow) :: above ∨
            (first, second) ∈ remaining.erase (wide, narrow) := by
        intro first firstIn second secondIn
        by_cases equal : (first, second) = (wide, narrow)
        · exact Or.inl (List.mem_cons.mpr (Or.inl equal))
        · rcases covered first firstIn second secondIn with old | new
          · exact Or.inl (List.mem_cons_of_mem _ old)
          · exact Or.inr ((List.mem_erase_of_ne equal).mpr new)
      conv => lhs; rw [check]
      conv => rhs; rw [check]
      simp only [ite_eq_right same, ite_eq_right seen]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.any_eq_true]
      apply forall_congr'
      intro edge
      apply forall_congr'
      intro edgeIn
      apply exists_congr
      intro cover
      apply and_congr_right
      intro coverIn
      have children : checkChildren (check automaton unconstrained fuel ((wide, narrow) :: above)) cover.children edge.children =
          checkChildren (check automaton unconstrained (fuel + 1) ((wide, narrow) :: above)) cover.children edge.children := by
        apply children_congr
        intro first firstIn second secondIn
        exact check_stable automaton unconstrained domain closed (remaining.erase (wide, narrow))
          ((wide, narrow) :: above) retained fuel reduced first second
          (closed wide wideIn cover coverIn first firstIn) (closed narrow narrowIn edge edgeIn second secondIn)
      rw [children]
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem present]
  omega

/-- Cartesian pairs of a child-closed local inventory give an explicit saturated search bound. -/
theorem check_saturated [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (unconstrained : Edge State Symbol → Bool)
    (states : List State) (closed : Closed automaton (· ∈ states))
    (wide narrow : State) (wideIn : wide ∈ states) (narrowIn : narrow ∈ states) (extra : Nat) :
    check automaton unconstrained (states.length * states.length + extra) [] wide narrow =
      check automaton unconstrained (states.length * states.length) [] wide narrow := by
  have pairs : ∀ first, first ∈ states → ∀ second, second ∈ states →
      (first, second) ∈ ([] : List (State × State)) ∨ (first, second) ∈ states.flatMap (fun first => states.map (first, ·)) := by
    intro first firstIn second secondIn
    exact Or.inr (List.mem_flatMap.mpr ⟨first, firstIn, List.mem_map.mpr ⟨second, secondIn, rfl⟩⟩)
  have pairCount : (states.flatMap (fun first => states.map (first, ·))).length = states.length * states.length := by
    simp only [List.length_flatMap, List.length_map]
    have count (xs : List State) (amount : Nat) : (xs.map (fun _ => amount)).sum = xs.length * amount := by
      induction xs with
      | nil => simp
      | cons first rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
    exact count states states.length
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [Nat.add_succ, ← check_stable automaton unconstrained (· ∈ states) closed
        (states.flatMap (fun first => states.map (first, ·))) [] pairs (states.length * states.length + extra)
        (by rw [pairCount]; omega) wide narrow wideIn narrowIn, ih]

end MicroCFTA.MergedComparisonInventory
