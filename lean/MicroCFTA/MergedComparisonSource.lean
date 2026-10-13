import MicroCFTA.MergedComparisonInventory

/-!
# The source coverage worker with both EmptyNode shortcuts

The Haskell worker accepts a literal empty narrow operand first. It then
rejects a literal empty wide operand. These tests precede identity and
ancestor-pair reuse. The finite local pair inventory bounds this exact
branch order as well as the row-only coverage model.
-/
namespace MicroCFTA.MergedComparisonSource
open Language MergedAlternativesSubsumption

/-- Follow the source's empty, identity, ancestor, and ordered edge branches. -/
def check [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (isEmpty : State → Bool) (unconstrained : Edge State Symbol → Bool) :
    Nat → List (State × State) → State → State → Bool
  | fuel, above, wide, narrow =>
      if isEmpty narrow then true
      else if isEmpty wide then false
      else if wide = narrow then true
      else if (wide, narrow) ∈ above then true
      else match fuel with
      | 0 => false
      | rest + 1 => (automaton narrow).all fun edge =>
          (automaton wide).any fun cover =>
            decide (cover.label = edge.label) && decide (cover.children.length = edge.children.length) && unconstrained cover &&
              checkChildren (check automaton isEmpty unconstrained rest ((wide, narrow) :: above))
                cover.children edge.children

/-- A finite call tree covers both comparison answers, including every child pair the source can demand. -/
inductive Terminates (automaton : Automaton State Symbol) (isEmpty : State → Bool) :
    List (State × State) → State → State → Prop where
  | narrowEmpty : isEmpty narrow = true → Terminates automaton isEmpty above wide narrow
  | wideEmpty : isEmpty wide = true → Terminates automaton isEmpty above wide narrow
  | same : Terminates automaton isEmpty above state state
  | seen : (wide, narrow) ∈ above → Terminates automaton isEmpty above wide narrow
  | expand
      (children : ∀ edge ∈ automaton narrow, ∀ cover ∈ automaton wide,
        ∀ first ∈ cover.children, ∀ second ∈ edge.children,
          Terminates automaton isEmpty ((wide, narrow) :: above) first second) :
      Terminates automaton isEmpty above wide narrow

/-- Every source comparison has a finite call tree when its local remaining pair list covers each recursive child. -/
theorem calls_finite [DecidableEq State] (automaton : Automaton State Symbol) (isEmpty : State → Bool)
    (domain : State → Prop) (closed : MergedComparisonInventory.Closed automaton domain)
    (remaining above : List (State × State))
    (covered : ∀ first, domain first → ∀ second, domain second →
      (first, second) ∈ above ∨ (first, second) ∈ remaining)
    (wide narrow : State) (wideIn : domain wide) (narrowIn : domain narrow) :
    Terminates automaton isEmpty above wide narrow := by
  by_cases narrowEmpty : isEmpty narrow = true
  · exact .narrowEmpty narrowEmpty
  by_cases wideEmpty : isEmpty wide = true
  · exact .wideEmpty wideEmpty
  by_cases same : wide = narrow
  · subst narrow; exact .same
  by_cases seen : (wide, narrow) ∈ above
  · exact .seen seen
  have present := (covered wide wideIn narrow narrowIn).resolve_left seen
  apply Terminates.expand
  intro edge edgeIn cover coverIn first firstIn second secondIn
  apply calls_finite automaton isEmpty domain closed (remaining.erase (wide, narrow)) ((wide, narrow) :: above)
  · intro left leftIn right rightIn
    by_cases equal : (left, right) = (wide, narrow)
    · exact Or.inl (List.mem_cons.mpr (Or.inl equal))
    · rcases covered left leftIn right rightIn with old | new
      · exact Or.inl (List.mem_cons_of_mem _ old)
      · exact Or.inr ((List.mem_erase_of_ne equal).mpr new)
  · exact closed wide wideIn cover coverIn first firstIn
  · exact closed narrow narrowIn edge edgeIn second secondIn
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

/-- A child-closed finite local state inventory derives termination without an assumed comparison result. -/
theorem inventory_terminates [DecidableEq State] (automaton : Automaton State Symbol) (isEmpty : State → Bool)
    (states : List State) (closed : MergedComparisonInventory.Closed automaton (· ∈ states))
    (wide narrow : State) (wideIn : wide ∈ states) (narrowIn : narrow ∈ states) :
    Terminates automaton isEmpty [] wide narrow := by
  apply calls_finite automaton isEmpty (· ∈ states) closed (states.flatMap (fun first => states.map (first, ·))) []
  · intro first firstIn second secondIn
    exact Or.inr (List.mem_flatMap.mpr ⟨first, firstIn, List.mem_map.mpr ⟨second, secondIn, rfl⟩⟩)
  · exact wideIn
  · exact narrowIn

/-- Source comparison stabilizes after exhausting the remaining pairs in its local child-closed domain. -/
theorem check_stable [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (isEmpty : State → Bool) (unconstrained : Edge State Symbol → Bool)
    (domain : State → Prop) (closed : MergedComparisonInventory.Closed automaton domain)
    (remaining above : List (State × State))
    (covered : ∀ first, domain first → ∀ second, domain second →
      (first, second) ∈ above ∨ (first, second) ∈ remaining)
    (fuel : Nat) (enough : remaining.length ≤ fuel) (wide narrow : State)
    (wideIn : domain wide) (narrowIn : domain narrow) :
    check automaton isEmpty unconstrained fuel above wide narrow =
      check automaton isEmpty unconstrained (fuel + 1) above wide narrow := by
  by_cases narrowEmpty : isEmpty narrow = true
  · cases fuel <;> simp [check, narrowEmpty]
  by_cases wideEmpty : isEmpty wide = true
  · cases fuel <;> simp [check, narrowEmpty, wideEmpty]
  by_cases same : wide = narrow
  · cases fuel <;> simp [check, narrowEmpty, same]
  by_cases seen : (wide, narrow) ∈ above
  · cases fuel <;> simp [check, narrowEmpty, wideEmpty, same, seen]
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
      simp only [ite_eq_right narrowEmpty, ite_eq_right wideEmpty, ite_eq_right same, ite_eq_right seen]
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
      have children : checkChildren (check automaton isEmpty unconstrained fuel ((wide, narrow) :: above)) cover.children edge.children =
          checkChildren (check automaton isEmpty unconstrained (fuel + 1) ((wide, narrow) :: above)) cover.children edge.children := by
        apply MergedComparisonInventory.children_congr
        intro first firstIn second secondIn
        exact check_stable automaton isEmpty unconstrained domain closed (remaining.erase (wide, narrow))
          ((wide, narrow) :: above) retained fuel reduced first second
          (closed wide wideIn cover coverIn first firstIn) (closed narrow narrowIn edge edgeIn second secondIn)
      rw [children]
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem present]
  omega

/-- A source comparison requires at most the square of the local physical inventory length. -/
theorem check_saturated [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (isEmpty : State → Bool) (unconstrained : Edge State Symbol → Bool)
    (states : List State) (closed : MergedComparisonInventory.Closed automaton (· ∈ states))
    (wide narrow : State) (wideIn : wide ∈ states) (narrowIn : narrow ∈ states) (extra : Nat) :
    check automaton isEmpty unconstrained (states.length * states.length + extra) [] wide narrow =
      check automaton isEmpty unconstrained (states.length * states.length) [] wide narrow := by
  let pairs := states.flatMap (fun first => states.map (first, ·))
  have covered : ∀ first, first ∈ states → ∀ second, second ∈ states →
      (first, second) ∈ ([] : List (State × State)) ∨ (first, second) ∈ pairs := by
    intro first firstIn second secondIn
    exact Or.inr (List.mem_flatMap.mpr ⟨first, firstIn, List.mem_map.mpr ⟨second, secondIn, rfl⟩⟩)
  have pairCount : pairs.length = states.length * states.length := by
    simp only [pairs, List.length_flatMap, List.length_map]
    have count (xs : List State) (amount : Nat) : (xs.map (fun _ => amount)).sum = xs.length * amount := by
      induction xs with
      | nil => simp
      | cons first rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
    exact count states states.length
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [Nat.add_succ, ← check_stable automaton isEmpty unconstrained (· ∈ states) closed
        pairs [] covered (states.length * states.length + extra)
        (by rw [pairCount]; omega) wide narrow wideIn narrowIn, ih]

/-- Literal emptiness can reject coverage even when both exposed edge lists are empty. -/
theorem empty_wide_boundary :
    check (fun _ : Bool => ([] : List (Edge Bool Unit))) id (fun _ => true) 1 [] true false = false ∧
      MergedAlternativesSubsumption.check (fun _ : Bool => ([] : List (Edge Bool Unit)))
        (fun _ => true) 1 [] true false = true := by decide

/-- A stronger successful child comparison remains successful after pointwise weakening. -/
theorem children_success (first second : State → State → Bool)
    (weakens : ∀ wide narrow, first wide narrow = true → second wide narrow = true)
    (wides narrows : List State) (success : checkChildren first wides narrows = true) :
    checkChildren second wides narrows = true := by
  induction wides generalizing narrows with
  | nil => cases narrows <;> simp_all [checkChildren]
  | cons wide wides ih =>
      cases narrows with
      | nil => simp [checkChildren] at success
      | cons narrow narrows =>
          have both := Bool.and_eq_true_iff.mp success
          exact Bool.and_eq_true_iff.mpr ⟨weakens wide narrow both.1, ih narrows both.2⟩

/-- Every successful exact source comparison yields a successful row-model comparison with one extra level. -/
theorem source_to_rows [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (isEmpty : State → Bool) (unconstrained : Edge State Symbol → Bool)
    (emptyRows : ∀ state, isEmpty state = true → automaton state = [])
    (fuel : Nat) (above : List (State × State)) (wide narrow : State)
    (success : check automaton isEmpty unconstrained fuel above wide narrow = true) :
    MergedAlternativesSubsumption.check automaton unconstrained (fuel + 1) above wide narrow = true := by
  by_cases narrowEmpty : isEmpty narrow = true
  · simp [MergedAlternativesSubsumption.check, emptyRows narrow narrowEmpty]
  by_cases wideEmpty : isEmpty wide = true
  · cases fuel <;> simp [check, narrowEmpty, wideEmpty] at success
  by_cases same : wide = narrow
  · simp [MergedAlternativesSubsumption.check, same]
  by_cases seen : (wide, narrow) ∈ above
  · simp [MergedAlternativesSubsumption.check, seen]
  cases fuel with
  | zero => simp [check, narrowEmpty, wideEmpty, same, seen] at success
  | succ fuel =>
      simp only [check, ite_eq_right narrowEmpty, ite_eq_right wideEmpty, ite_eq_right same, ite_eq_right seen] at success
      rw [MergedAlternativesSubsumption.check]
      simp only [ite_eq_right same, ite_eq_right seen]
      apply List.all_eq_true.mpr
      intro edge member
      obtain ⟨cover, coverIn, selected⟩ := List.any_eq_true.mp (List.all_eq_true.mp success edge member)
      have parts := Bool.and_eq_true_iff.mp selected
      have header := Bool.and_eq_true_iff.mp parts.1
      have label := (Bool.and_eq_true_iff.mp header.1).1
      apply List.any_eq_true.mpr
      refine ⟨cover, coverIn, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨label, header.2⟩, ?_⟩⟩
      exact children_success _ _ (source_to_rows automaton isEmpty unconstrained emptyRows fuel
        ((wide, narrow) :: above)) cover.children edge.children parts.2
termination_by fuel

/-- Successful source coverage retains the original finite-term language guarantee. -/
theorem check_sound [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (isEmpty : State → Bool) (unconstrained : Edge State Symbol → Bool)
    (emptyRows : ∀ state, isEmpty state = true → automaton state = [])
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (fuel : Nat) (wide narrow : State) (success : check automaton isEmpty unconstrained fuel [] wide narrow = true)
    (term : Term Symbol) (accepted : Accepts automaton narrow term) : Accepts automaton wide term :=
  MergedAlternativesSubsumption.check_sound automaton unconstrained clear (fuel + 1) wide narrow
    (source_to_rows automaton isEmpty unconstrained emptyRows fuel [] wide narrow success) term accepted

end MicroCFTA.MergedComparisonSource
