import MicroCFTA.KeyedProbability

/-!
# Attained minima of typed recursive key families

The concrete key-discovery driver carries actual typed value witnesses.
This connects its metadata-only minimum calculation to the typed finite
derivation language and justifies the final productive-key filter.
-/

namespace MicroCFTA.KeyedMinimumWitness
open KeyedSource

/-- A singleton optional minimum has exactly that list minimum. -/
theorem option_minimum (minimum : Option Nat) : minimum.toList.min? = minimum := by cases minimum <;> rfl

/-- Every stored finite key minimum has a typed source member at that exact size. -/
def Sound (program : Key → Recipe Key Root Root) (known : GroupedProbe.Table Key) : Prop :=
  ∀ key size, known key = some (some size) → ∃ value, Derives program (program key) value size

/-- Computing a body minimum constructs a typed witness from witnessed occurrence minima. -/
theorem evaluate_attains (program : Key → Recipe Key Root Root) (known : GroupedProbe.Table Key)
    (sound : Sound program known) (recipe : Recipe Key Root α) (size : Nat)
    (found : GroupedMinimum.evaluate (minimumExpr recipe) known = some (some size)) :
    ∃ value, Derives program recipe value size := by
  induction recipe generalizing size with
  | finite source =>
      have minimum : SourceMinimum.minimum source = some size := by
        simpa [minimumExpr, GroupedMinimum.evaluate, option_minimum] using found
      obtain ⟨value, member⟩ := MinimumWitness.finite_attains source size minimum
      exact ⟨value, .finite source value size member⟩
  | retained mass positive source =>
      have minimum : SourceMinimum.minimum source = some size := by
        simpa [minimumExpr, GroupedMinimum.evaluate, option_minimum] using found
      obtain ⟨value, member⟩ := MinimumWitness.finite_attains source size minimum
      exact ⟨value, .retained mass positive source value size member⟩
  | occurrence key =>
      obtain ⟨value, derived⟩ := sound key size found
      exact ⟨value, .occurrence key value size derived⟩
  | map transform inner ih =>
      obtain ⟨value, derived⟩ := ih size found
      exact ⟨transform value, .map transform inner value size derived⟩
  | pay inner ih =>
      cases outer : GroupedMinimum.evaluate (minimumExpr inner) known with
      | none => simp [minimumExpr, GroupedMinimum.evaluate, outer] at found
      | some minimum =>
          cases minimum with
          | none => simp [minimumExpr, GroupedMinimum.evaluate, outer] at found
          | some smaller =>
              have same : size = smaller + 1 := by simpa [minimumExpr, GroupedMinimum.evaluate, outer] using found.symm
              obtain ⟨value, derived⟩ := ih smaller outer
              exact ⟨value, same ▸ Derives.pay inner value smaller derived⟩
  | choice left right ihl ihr =>
      rcases GroupedMinimum.join_finite _ _ size found with fromLeft | fromRight
      · obtain ⟨value, derived⟩ := ihl size fromLeft
        exact ⟨value, .left left right value size derived⟩
      · obtain ⟨value, derived⟩ := ihr size fromRight
        exact ⟨value, .right left right value size derived⟩
  | ap functions arguments ihf iha =>
      cases leftEntry : GroupedMinimum.evaluate (minimumExpr functions) known with
      | none => simp [minimumExpr, GroupedMinimum.evaluate, GroupedMinimum.productEntry, leftEntry] at found
      | some leftMinimum =>
          cases rightEntry : GroupedMinimum.evaluate (minimumExpr arguments) known with
          | none => simp [minimumExpr, GroupedMinimum.evaluate, GroupedMinimum.productEntry, leftEntry, rightEntry] at found
          | some rightMinimum =>
              cases leftMinimum with
              | none => simp [minimumExpr, GroupedMinimum.evaluate, GroupedMinimum.productEntry, RecursionProbe.productMinimum, leftEntry, rightEntry] at found
              | some leftSize =>
                  cases rightMinimum with
                  | none => simp [minimumExpr, GroupedMinimum.evaluate, GroupedMinimum.productEntry, RecursionProbe.productMinimum, leftEntry, rightEntry] at found
                  | some rightSize =>
                      have same : size = leftSize + rightSize := by
                        simpa [minimumExpr, GroupedMinimum.evaluate, GroupedMinimum.productEntry, RecursionProbe.productMinimum, leftEntry, rightEntry] using found.symm
                      obtain ⟨function, leftDerived⟩ := ihf leftSize leftEntry
                      obtain ⟨argument, rightDerived⟩ := iha rightSize rightEntry
                      exact ⟨function argument, same ▸ Derives.ap functions arguments function argument _ _ leftDerived rightDerived⟩

/-- Actual typed witnesses survive every key-map union and minimum improvement. -/
theorem step_sound (program : Key → Recipe Key Root Root) (known : GroupedProbe.Table Key)
    (sound : Sound program known) : Sound program (GroupedProbe.step (GroupedMinimum.build (minimumProgram program)) known) := by
  intro key size found
  rcases GroupedMinimum.join_finite _ _ size found with previous | rebuilt
  · exact sound key size previous
  · exact evaluate_attains program known sound (program key) size rebuilt

/-- The complete discovery loop preserves typed witnesses without a productivity premise. -/
theorem converge_sound (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root)
    (known : GroupedProbe.Table Key) (sound : Sound program known) :
    Sound program (GroupedProbe.converge keys complete (GroupedMinimum.build (minimumProgram program)) known) := by
  induction known using GroupedProbe.converge.induct keys complete (GroupedMinimum.build (minimumProgram program)) with
  | case1 known grown stable =>
      dsimp only [grown] at stable
      rw [GroupedProbe.converge.eq_def]
      simpa only [dite_eq_left stable] using sound
  | case2 known grown unstable ih =>
      dsimp only [grown] at unstable
      rw [GroupedProbe.converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih (step_sound program known sound)

/-- A reported finite key minimum is attained by an actual typed value. -/
theorem minima_attained (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root) :
    Sound program (minima keys complete program) :=
  converge_sound keys complete program _ (by intro key size found; cases found)

/-- Each finite typed derivation causes its key to be discovered with a minimum at or below its size. -/
theorem minima_complete (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root)
    (key : Key) (value : Root) (size : Nat) (derived : Derives program (program key) value size) :
    ∃ lower, minima keys complete program key = some (some lower) ∧ lower ≤ size := by
  obtain ⟨lower, found, bound⟩ := derivation_minimum keys complete program (program key) value size derived
  have fixed := GroupedProbe.converge_fixed keys complete (GroupedMinimum.build (minimumProgram program)) (fun _ => none)
  obtain ⟨smaller, kept, smallerBound⟩ := GroupedMinimum.stable_bound (minimumProgram program)
    (minima keys complete program) fixed key lower found
  exact ⟨smaller, kept, by omega⟩

/-- The actual source key minimum is exactly the least attained typed member size. -/
theorem minima_exact (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root)
    (key : Key) (size : Nat) :
    minima keys complete program key = some (some size) ↔
      (∃ value, Derives program (program key) value size) ∧
        ∀ value other, Derives program (program key) value other → size ≤ other := by
  constructor
  · intro found
    refine ⟨minima_attained keys complete program key size found, ?_⟩
    intro value other derived
    obtain ⟨lower, kept, bound⟩ := minima_complete keys complete program key value other derived
    have same := Option.some.inj (Option.some.inj (found.symm.trans kept))
    exact same ▸ bound
  · rintro ⟨⟨value, derived⟩, minimal⟩
    obtain ⟨lower, found, bound⟩ := minima_complete keys complete program key value size derived
    obtain ⟨witness, attained⟩ := minima_attained keys complete program key lower found
    have reverse := minimal witness lower attained
    have same : lower = size := by omega
    exact same ▸ found

/-- Filtering absent minima retains every productive typed key and removes only empty key languages. -/
theorem liveKeys_exact (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root) (key : Key) :
    key ∈ GroupedMinimum.liveKeys keys (minima keys complete program) ↔
      ∃ value size, Derives program (program key) value size := by
  constructor
  · intro present
    have finite := (List.mem_filter.mp present).2
    cases found : minima keys complete program key with
    | none => simp [found] at finite
    | some minimum =>
        cases minimum with
        | none => simp [found] at finite
        | some size =>
            obtain ⟨value, derived⟩ := minima_attained keys complete program key size found
            exact ⟨value, size, derived⟩
  · rintro ⟨value, size, derived⟩
    obtain ⟨lower, found, _⟩ := minima_complete keys complete program key value size derived
    simp [GroupedMinimum.liveKeys, complete, found]

end MicroCFTA.KeyedMinimumWitness
