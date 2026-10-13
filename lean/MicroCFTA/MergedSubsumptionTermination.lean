import MicroCFTA.MergedAlternativesSubsumption

/-!
# A finite pair inventory bounds recursive coverage search

Every unvisited comparison adds its pair to the ancestor list. A finite
inventory of all remaining pairs therefore bounds the required search
depth. This does not establish a finite physical node inventory for every
Haskell recursive unfolding.
-/
namespace MicroCFTA.MergedSubsumptionTermination
open Language MergedAlternativesSubsumption

/-- Removing the current unvisited pair preserves coverage by ancestors and remaining pairs. -/
theorem erase_coverage [DecidableEq State] (above remaining : List (State × State))
    (wide narrow : State)
    (covered : ∀ first second, (first, second) ∈ above ∨ (first, second) ∈ remaining) :
    ∀ first second, (first, second) ∈ (wide, narrow) :: above ∨
      (first, second) ∈ remaining.erase (wide, narrow) := by
  intro first second
  by_cases same : (first, second) = (wide, narrow)
  · exact Or.inl (List.mem_cons.mpr (Or.inl same))
  · rcases covered first second with old | new
    · exact Or.inl (List.mem_cons_of_mem _ old)
    · exact Or.inr ((List.mem_erase_of_ne same).mpr new)

/-- Fuel at least the remaining pair count makes one more search level irrelevant. -/
theorem check_stable [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (unconstrained : Edge State Symbol → Bool)
    (remaining above : List (State × State))
    (covered : ∀ first second, (first, second) ∈ above ∨ (first, second) ∈ remaining)
    (fuel : Nat) (enough : remaining.length ≤ fuel) (wide narrow : State) :
    check automaton unconstrained fuel above wide narrow =
      check automaton unconstrained (fuel + 1) above wide narrow := by
  by_cases same : wide = narrow
  · cases fuel <;> simp [check, same]
  by_cases seen : (wide, narrow) ∈ above
  · cases fuel <;> simp [check, same, seen]
  have present := (covered wide narrow).resolve_left seen
  have nonempty : 0 < remaining.length := List.length_pos_of_mem present
  have smaller : (remaining.erase (wide, narrow)).length < remaining.length := by
    rw [List.length_erase_of_mem present]
    omega
  cases fuel with
  | zero => omega
  | succ fuel =>
      have reduced : (remaining.erase (wide, narrow)).length ≤ fuel := by
        rw [List.length_erase_of_mem present]
        omega
      have functions : check automaton unconstrained fuel ((wide, narrow) :: above) =
          check automaton unconstrained (fuel + 1) ((wide, narrow) :: above) := by
        funext first second
        exact check_stable automaton unconstrained (remaining.erase (wide, narrow))
          ((wide, narrow) :: above) (erase_coverage above remaining wide narrow covered)
          fuel reduced first second
      conv => lhs; rw [check]
      conv => rhs; rw [check]
      simp only [ite_eq_right same, ite_eq_right seen]
      rw [functions]
termination_by remaining.length

/-- Every larger fuel budget gives the same comparison result once the pair inventory is covered. -/
theorem check_saturated [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (unconstrained : Edge State Symbol → Bool)
    (remaining above : List (State × State))
    (covered : ∀ first second, (first, second) ∈ above ∨ (first, second) ∈ remaining)
    (fuel extra : Nat) (enough : remaining.length ≤ fuel) (wide narrow : State) :
    check automaton unconstrained (fuel + extra) above wide narrow =
      check automaton unconstrained fuel above wide narrow := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [Nat.add_succ, ← check_stable automaton unconstrained remaining above covered
        (fuel + extra) (by omega) wide narrow, ih]

end MicroCFTA.MergedSubsumptionTermination
