import MicroCFTA.HeightOrder

/-!
# Initial bounds for controlled finite vector descent

Each state bounds its own vector coordinates by its current control number.
The next control number increases and is at most the control function.
Highest-coordinate blocks give an initial computable length bound. Lower
coordinates can grow after a higher-coordinate decrease.
-/
namespace MicroCFTA.HeightOrderControlled

/-- Apply a numeric function a fixed number of times in source order. -/
def iterate (next : Nat → Nat) : Nat → Nat → Nat
  | 0, value => value
  | count + 1, value => iterate next count (next value)

private theorem iterate_ge (next : Nat → Nat) (grows : ∀ value, value ≤ next value)
    (count value : Nat) : value ≤ iterate next count value := by
  induction count generalizing value with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (grows value) (ih (next value))

private theorem iterate_mono (next : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → next first ≤ next last) (count : Nat)
    {first last : Nat} (increase : first ≤ last) : iterate next count first ≤ iterate next count last := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih (mono increase)

private theorem iterate_add (next : Nat → Nat) (first last value : Nat) :
    iterate next (first + last) value = iterate next last (iterate next first value) := by
  induction first generalizing value with
  | zero => simp only [Nat.zero_add, iterate]
  | succ first ih => simpa only [Nat.succ_add, iterate] using ih (next value)

private theorem iterate_count_mono (next : Nat → Nat) (grows : ∀ value, value ≤ next value)
    {first last : Nat} (counts : first ≤ last) (value : Nat) :
    iterate next first value ≤ iterate next last value := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
  rw [iterate_add]
  exact iterate_ge next grows extra _

/-- The initial dimension and control number bound all later control numbers. -/
def majorant (control : Nat → Nat) : Nat → Nat → Nat
  | 0, value => value
  | dimension + 1, value =>
      iterate (fun current => control (majorant control dimension current)) (value + 1) value

/-- Zero-dimensional descent has no strict step. -/
theorem majorant_zero (control : Nat → Nat) (value : Nat) : majorant control 0 value = value := rfl

/-- Each higher dimension permits one block for every initial highest-coordinate value. -/
theorem majorant_succ (control : Nat → Nat) (dimension value : Nat) :
    majorant control (dimension + 1) value =
      iterate (fun current => control (majorant control dimension current)) (value + 1) value := rfl

/-- Every majorant retains the initial control number. -/
theorem majorant_ge (control : Nat → Nat) (grows : ∀ value, value < control value)
    (dimension value : Nat) : value ≤ majorant control dimension value := by
  induction dimension generalizing value with
  | zero => exact Nat.le_refl _
  | succ dimension ih =>
    exact iterate_ge _ (fun current => Nat.le_trans (ih current) (Nat.le_of_lt (grows _))) _ _

/-- A larger initial control number retains the same-dimensional majorant. -/
theorem majorant_mono (control : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → control first ≤ control last)
    (grows : ∀ value, value < control value) (dimension : Nat)
    {first last : Nat} (increase : first ≤ last) :
    majorant control dimension first ≤ majorant control dimension last := by
  induction dimension generalizing first last with
  | zero => exact increase
  | succ dimension ih =>
    have nextMono : ∀ {first last}, first ≤ last →
        control (majorant control dimension first) ≤ control (majorant control dimension last) :=
      fun enough => mono (ih enough)
    have nextGrows : ∀ current, current ≤ control (majorant control dimension current) :=
      fun current => Nat.le_trans (majorant_ge control grows dimension current) (Nat.le_of_lt (grows _))
    exact Nat.le_trans (iterate_mono _ nextMono _ increase)
      (iterate_count_mono _ nextGrows (Nat.succ_le_succ increase) last)

/-- A finite descending vector path retains each state's own numeric control. -/
inductive Path (control : Nat → Nat) (dimension : Nat) :
    (Nat → Nat) → Nat → (Nat → Nat) → Nat → Nat → Prop where
  /-- An empty path checks only its initial coordinate bounds. -/
  | refl (bounded : ∀ index, index < dimension → first index ≤ firstControl) :
      Path control dimension first firstControl first firstControl 0
  /-- One strict vector step increases control within the stated function. -/
  | step (bounded : ∀ index, index < dimension → first index ≤ firstControl)
      (decrease : HeightOrder.Below dimension middle first)
      (progress : firstControl < middleControl) (controlled : middleControl ≤ control firstControl)
      (tail : Path control dimension middle middleControl last lastControl length) :
      Path control dimension first firstControl last lastControl (length + 1)

/-- The initial vector is bounded by its own control number. -/
theorem Path.initial_bound {control : Nat → Nat} {dimension firstControl lastControl length : Nat}
    {first last : Nat → Nat} (actual : Path control dimension first firstControl last lastControl length) :
    ∀ index, index < dimension → first index ≤ firstControl := by
  cases actual with
  | refl bounded => exact bounded
  | step bounded _ _ _ _ => exact bounded

/-- Every strict control step pays one unit of elapsed path length. -/
theorem Path.elapsed_le {control : Nat → Nat} {dimension firstControl lastControl length : Nat}
    {first last : Nat → Nat} (actual : Path control dimension first firstControl last lastControl length) :
    firstControl + length ≤ lastControl := by
  induction actual with
  | refl => exact Nat.le_refl _
  | step bounded decrease progress controlled tail ih => omega

private theorem blocks {control : Nat → Nat} {dimension firstControl lastControl length : Nat}
    {first last : Nat → Nat} (actual : Path control (dimension + 1) first firstControl last lastControl length) :
    Path control dimension first firstControl last lastControl length ∨
      ∃ middle boundary middleControl boundaryControl prefixLength tailLength,
        Path control dimension first firstControl middle middleControl prefixLength ∧
        boundaryControl ≤ control middleControl ∧ boundary dimension < first dimension ∧
        Path control (dimension + 1) boundary boundaryControl last lastControl tailLength := by
  induction actual with
  | refl bounded => exact .inl (.refl (fun index inside => bounded index (by omega)))
  | @step first firstControl middle middleControl last lastControl length bounded decrease progress controlled tail ih =>
    have comparison : middle dimension < first dimension ∨
        middle dimension = first dimension ∧ HeightOrder.Below dimension middle first :=
      Prod.lex_def.mp decrease
    rcases comparison with smaller | ⟨same, lower⟩
    · exact .inr ⟨first, middle, firstControl, middleControl, 0, length,
        .refl (fun index inside => bounded index (by omega)), controlled, smaller, tail⟩
    · rcases ih with whole | ⟨earlierVector, boundary, prefixControl, boundaryControl, prefixLength, tailLength,
          earlierPath, nextControl, strict, remaining⟩
      · exact .inl (.step (fun index inside => bounded index (by omega)) lower progress controlled whole)
      · exact .inr ⟨earlierVector, boundary, prefixControl, boundaryControl, prefixLength + 1, tailLength,
          .step (fun index inside => bounded index (by omega)) lower progress controlled earlierPath,
          nextControl, by omega, remaining⟩

private theorem top_bound (control : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → control first ≤ control last)
    (grows : ∀ value, value < control value) (dimension : Nat)
    (lower : ∀ {first last firstControl lastControl length},
      Path control dimension first firstControl last lastControl length →
        lastControl ≤ majorant control dimension firstControl)
    (top : Nat) {first last : Nat → Nat} {firstControl lastControl length : Nat}
    (actual : Path control (dimension + 1) first firstControl last lastControl length)
    (bounded : first dimension ≤ top) :
    lastControl ≤ iterate (fun current => control (majorant control dimension current)) (top + 1) firstControl := by
  have nextMono : ∀ {first last}, first ≤ last →
      control (majorant control dimension first) ≤ control (majorant control dimension last) :=
    fun increase => mono (majorant_mono control mono grows dimension increase)
  have nextGrows : ∀ current, current ≤ control (majorant control dimension current) :=
    fun current => Nat.le_trans (majorant_ge control grows dimension current) (Nat.le_of_lt (grows _))
  induction top generalizing first last firstControl lastControl length with
  | zero =>
    rcases blocks actual with allLower | ⟨middle, boundary, middleControl, boundaryControl,
        prefixLength, tailLength, earlier, controlled, smaller, tail⟩
    · exact Nat.le_trans (lower allLower) (Nat.le_of_lt (grows _))
    · omega
  | succ top ih =>
    rcases blocks actual with allLower | ⟨middle, boundary, middleControl, boundaryControl,
        prefixLength, tailLength, earlier, controlled, smaller, tail⟩
    · exact Nat.le_trans (lower allLower) (Nat.le_trans (Nat.le_of_lt (grows _))
        (iterate_ge _ nextGrows (top + 1) _))
    · have endpoint := ih tail (show boundary dimension ≤ top by omega)
      have boundaryBound := Nat.le_trans controlled (mono (lower earlier))
      exact Nat.le_trans endpoint (iterate_mono _ nextMono (top + 1) boundaryBound)

/-- The initial controlled vector bounds every later control number on the finite path. -/
theorem Path.final_le {control : Nat → Nat}
    (mono : ∀ {first last}, first ≤ last → control first ≤ control last)
    (grows : ∀ value, value < control value)
    {dimension firstControl lastControl length : Nat} {first last : Nat → Nat}
    (actual : Path control dimension first firstControl last lastControl length) :
    lastControl ≤ majorant control dimension firstControl := by
  induction dimension generalizing first last firstControl lastControl length with
  | zero =>
    cases actual with
    | refl => exact Nat.le_refl _
    | step bounded decrease progress controlled tail => exact False.elim decrease
  | succ dimension ih =>
    exact top_bound control mono grows dimension (fun earlier => ih earlier) firstControl actual
      (actual.initial_bound dimension (by omega))

/-- The initial controlled-vector majorant bounds the number of actual strict steps. -/
theorem Path.length_le {control : Nat → Nat}
    (mono : ∀ {first last}, first ≤ last → control first ≤ control last)
    (grows : ∀ value, value < control value)
    {dimension firstControl lastControl length : Nat} {first last : Nat → Nat}
    (actual : Path control dimension first firstControl last lastControl length) :
    length ≤ majorant control dimension firstControl :=
  Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) actual.elapsed_le) (actual.final_le mono grows)

end MicroCFTA.HeightOrderControlled
