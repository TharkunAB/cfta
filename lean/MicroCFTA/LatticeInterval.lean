import MicroCFTA.LatticeBound
import MicroCFTA.Lattice

/-!
# Integer interval extraction from substituted regions

The source substitutes the earlier variables before it extracts the interval
of the current variable. The `Only` premise states the resulting support
invariant. Coefficients can be arbitrary integers. Floor division supplies
the exact lower and upper integer endpoints.
-/

namespace MicroCFTA.LatticeInterval

open LatticeLinear

/-- A substituted form contains at most the current variable. -/
def Only (index : Nat) (linear : Linear) : Prop :=
  ∀ entry ∈ linear.coefficients, entry.1 = index

/-- Deleting the only remaining variable leaves a constant form. -/
theorem delete_only (index : Nat) (linear : Linear) (only : Only index linear) :
    (LatticeBound.deleteVariable index linear).coefficients = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry member
  have same := only entry member
  simp [same]

/-- A form with one variable evaluates to the selected coefficient times its value plus its offset. -/
theorem evaluate_only (assignment : Nat → Int) (index : Nat) (value : Int) (linear : Linear)
    (valid : Valid linear) (only : Only index linear) :
    evaluate (LatticeBound.update assignment index value) linear =
      LatticeBound.coefficientOf index linear * value + linear.offset := by
  rw [LatticeBound.evaluate_decompose assignment index value linear valid]
  have deleted := delete_only index linear only
  unfold evaluate
  rw [deleted]
  simp [evalCoefficients, LatticeBound.deleteVariable]

/-- Floor division gives the exact lower integer endpoint for a positive coefficient. -/
theorem lower_division (coefficient offset value : Int) (positive : 0 < coefficient) :
    (0 ≤ coefficient * value + offset) ↔ -(offset / coefficient) ≤ value := by
  rw [Lattice.normalize_divisor coefficient value offset positive]
  omega

/-- Floor division gives the exact upper integer endpoint for a negative coefficient. -/
theorem upper_division (coefficient offset value : Int) (negative : coefficient < 0) :
    (0 ≤ coefficient * value + offset) ↔ value ≤ offset / (-coefficient) := by
  have positive : 0 < -coefficient := by omega
  have same : coefficient * value + offset = (-coefficient) * (-value) + offset := by grind
  rw [same, Lattice.normalize_divisor (-coefficient) (-value) offset positive]
  omega

/-- The interval endpoints can be unknown until a bound is encountered. -/
abbrev Bounds := Option Int × Option Int

/-- A missing state is inconsistent. Missing endpoints place no restriction. -/
def contains : Option Bounds → Int → Prop
  | none, _ => False
  | some (low, high), value =>
    (match low with | none => True | some bound => bound ≤ value) ∧
    (match high with | none => True | some bound => value ≤ bound)

/-- Tighten a lower endpoint by taking the larger bound. -/
def tightenLow (old : Option Int) (bound : Int) : Option Int := some (old.map (max bound) |>.getD bound)

/-- Tighten an upper endpoint by taking the smaller bound. -/
def tightenHigh (old : Option Int) (bound : Int) : Option Int := some (old.map (min bound) |>.getD bound)

/-- Process one substituted inequality exactly as the source's `narrow`. -/
def narrow (index : Nat) (linear : Linear) : Option Bounds → Option Bounds
  | none => none
  | some (low, high) =>
    let coefficient := LatticeBound.coefficientOf index linear
    if coefficient = 0 then
      if 0 ≤ linear.offset then some (low, high) else none
    else if 0 < coefficient then some (tightenLow low (-(linear.offset / coefficient)), high)
    else some (low, tightenHigh high (linear.offset / (-coefficient)))

/-- Tightening a lower bound intersects the represented interval with that inequality. -/
theorem contains_tightenLow (low high : Option Int) (bound value : Int) :
    contains (some (tightenLow low bound, high)) value ↔ contains (some (low, high)) value ∧ bound ≤ value := by
  cases low <;> cases high <;> simp [contains, tightenLow] <;> omega

/-- Tightening an upper bound intersects the represented interval with that inequality. -/
theorem contains_tightenHigh (low high : Option Int) (bound value : Int) :
    contains (some (low, tightenHigh high bound)) value ↔ contains (some (low, high)) value ∧ value ≤ bound := by
  cases low <;> cases high <;> simp [contains, tightenHigh] <;> omega

/-- Every narrowing step preserves exactly the integer solutions of its form and prior state. -/
theorem narrow_correct (assignment : Nat → Int) (index : Nat) (linear : Linear)
    (valid : Valid linear) (only : Only index linear) (state : Option Bounds) (value : Int) :
    contains (narrow index linear state) value ↔
      contains state value ∧ 0 ≤ evaluate (LatticeBound.update assignment index value) linear := by
  rw [evaluate_only assignment index value linear valid only]
  cases state with
  | none => simp [narrow, contains]
  | some endpoints =>
    rcases endpoints with ⟨low, high⟩
    unfold narrow
    by_cases zero : LatticeBound.coefficientOf index linear = 0
    · simp only [zero, ↓reduceIte, Int.zero_mul, Int.zero_add]
      split
      · next nonnegative => simp [nonnegative]
      · next negative => simp [negative, contains]
    · simp only [zero, ↓reduceIte]
      split
      · next positive =>
        rw [contains_tightenLow, lower_division _ _ _ positive]
      · next negative =>
        rw [contains_tightenHigh, upper_division _ _ _ (by omega)]

/-- Fold all substituted region inequalities into one interval state. -/
def foldBounds (index : Nat) (forms : List Linear) : Option Bounds :=
  forms.foldr (narrow index) (some (none, none))

/-- Folding retains exactly the conjunction of all integer inequalities. -/
theorem foldBounds_correct (assignment : Nat → Int) (index : Nat) (forms : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (only : ∀ form ∈ forms, Only index form) (value : Int) :
    contains (foldBounds index forms) value ↔
      ∀ form ∈ forms, 0 ≤ evaluate (LatticeBound.update assignment index value) form := by
  induction forms with
  | nil => simp [foldBounds, contains]
  | cons form rest ih =>
    change contains (narrow index form (foldBounds index rest)) value ↔ _
    rw [narrow_correct assignment index form (valid form (by simp)) (only form (by simp)),
      ih (fun item member => valid item (by simp [member])) (fun item member => only item (by simp [member]))]
    simp only [List.forall_mem_cons]
    exact and_comm

/-- Return known nonempty endpoints, as the source's `interval` does. -/
def interval (index : Nat) (forms : List Linear) : Option (Int × Int) :=
  match foldBounds index forms with
  | some (some low, some high) => if low ≤ high then some (low, high) else none
  | _ => none

/-- Every returned interval is nonempty. -/
theorem interval_ordered (index : Nat) (forms : List Linear) (low high : Int)
    (success : interval index forms = some (low, high)) : low ≤ high := by
  unfold interval at success
  split at success
  · split at success
    · cases success; assumption
    · cases success
  · cases success

/-- Successful extraction has exact support, including negative bounds and non-unit coefficients. -/
theorem interval_correct (assignment : Nat → Int) (index : Nat) (forms : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (only : ∀ form ∈ forms, Only index form)
    (low high value : Int) (success : interval index forms = some (low, high)) :
    (∀ form ∈ forms, 0 ≤ evaluate (LatticeBound.update assignment index value) form) ↔ low ≤ value ∧ value ≤ high := by
  rw [← foldBounds_correct assignment index forms valid only value]
  unfold interval at success
  split at success
  · next a b found =>
    split at success
    · cases success
      rw [found]
      rfl
    · cases success
  · cases success

/-- A known lower endpoint is retained, and a positive coefficient establishes one. -/
theorem narrow_lower_known (index : Nat) (linear : Linear) (oldLow oldHigh low high : Option Int)
    (success : narrow index linear (some (oldLow, oldHigh)) = some (low, high))
    (known : oldLow ≠ none ∨ 0 < LatticeBound.coefficientOf index linear) : low ≠ none := by
  simp only [narrow] at success
  split at success
  · next zero =>
    split at success
    · cases success; rcases known with known | positive; exact known; omega
    · cases success
  · split at success
    · cases success; simp [tightenLow]
    · next nonpositive =>
      cases success
      rcases known with known | positive
      · exact known
      · exact False.elim (nonpositive positive)

/-- A known upper endpoint is retained, and a negative coefficient establishes one. -/
theorem narrow_upper_known (index : Nat) (linear : Linear) (oldLow oldHigh low high : Option Int)
    (success : narrow index linear (some (oldLow, oldHigh)) = some (low, high))
    (known : oldHigh ≠ none ∨ LatticeBound.coefficientOf index linear < 0) : high ≠ none := by
  simp only [narrow] at success
  split at success
  · next zero =>
    split at success
    · cases success; rcases known with known | negative; exact known; omega
    · cases success
  · split at success
    · next positive =>
      cases success
      rcases known with known | negative
      · exact known
      · omega
    · cases success; simp [tightenHigh]

/-- A positive coefficient supplies a lower endpoint in every successful fold. -/
theorem foldBounds_lower (index : Nat) (forms : List Linear) (low high : Option Int)
    (success : foldBounds index forms = some (low, high))
    (positive : ∃ form ∈ forms, 0 < LatticeBound.coefficientOf index form) : low ≠ none := by
  induction forms generalizing low high with
  | nil => obtain ⟨form, member, _⟩ := positive; simp at member
  | cons form rest ih =>
    change narrow index form (foldBounds index rest) = some (low, high) at success
    cases tail : foldBounds index rest with
    | none => simp [tail, narrow] at success
    | some endpoints =>
      rcases endpoints with ⟨oldLow, oldHigh⟩
      rw [tail] at success
      apply narrow_lower_known index form oldLow oldHigh low high success
      obtain ⟨selected, member, coefficient⟩ := positive
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact Or.inr coefficient
      · exact Or.inl (ih oldLow oldHigh tail ⟨selected, member, coefficient⟩)

/-- A negative coefficient supplies an upper endpoint in every successful fold. -/
theorem foldBounds_upper (index : Nat) (forms : List Linear) (low high : Option Int)
    (success : foldBounds index forms = some (low, high))
    (negative : ∃ form ∈ forms, LatticeBound.coefficientOf index form < 0) : high ≠ none := by
  induction forms generalizing low high with
  | nil => obtain ⟨form, member, _⟩ := negative; simp at member
  | cons form rest ih =>
    change narrow index form (foldBounds index rest) = some (low, high) at success
    cases tail : foldBounds index rest with
    | none => simp [tail, narrow] at success
    | some endpoints =>
      rcases endpoints with ⟨oldLow, oldHigh⟩
      rw [tail] at success
      apply narrow_upper_known index form oldLow oldHigh low high success
      obtain ⟨selected, member, coefficient⟩ := negative
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact Or.inr coefficient
      · exact Or.inl (ih oldLow oldHigh tail ⟨selected, member, coefficient⟩)

/-- Both bound directions make extraction complete for every satisfying integer. -/
theorem interval_complete (assignment : Nat → Int) (index : Nat) (forms : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (only : ∀ form ∈ forms, Only index form)
    (positive : ∃ form ∈ forms, 0 < LatticeBound.coefficientOf index form)
    (negative : ∃ form ∈ forms, LatticeBound.coefficientOf index form < 0)
    (value : Int) (satisfies : ∀ form ∈ forms, 0 ≤ evaluate (LatticeBound.update assignment index value) form) :
    ∃ low high, interval index forms = some (low, high) ∧ low ≤ value ∧ value ≤ high := by
  have included := (foldBounds_correct assignment index forms valid only value).mpr satisfies
  cases folded : foldBounds index forms with
  | none => simp [folded, contains] at included
  | some endpoints =>
    rcases endpoints with ⟨low, high⟩
    have lowerKnown := foldBounds_lower index forms low high folded positive
    have upperKnown := foldBounds_upper index forms low high folded negative
    cases low with
    | none => exact False.elim (lowerKnown rfl)
    | some low =>
      cases high with
      | none => exact False.elim (upperKnown rfl)
      | some high =>
        rw [folded] at included
        change low ≤ value ∧ value ≤ high at included
        refine ⟨low, high, ?_, included⟩
        unfold interval
        rw [folded]
        simp [show low ≤ high by omega]

/-- With both bound directions present, an omitted interval has no satisfying integer. -/
theorem interval_none (assignment : Nat → Int) (index : Nat) (forms : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (only : ∀ form ∈ forms, Only index form)
    (positive : ∃ form ∈ forms, 0 < LatticeBound.coefficientOf index form)
    (negative : ∃ form ∈ forms, LatticeBound.coefficientOf index form < 0)
    (failure : interval index forms = none) :
    ∀ value, ¬ (∀ form ∈ forms, 0 ≤ evaluate (LatticeBound.update assignment index value) form) := by
  intro value satisfies
  obtain ⟨low, high, found, _⟩ := interval_complete assignment index forms valid only positive negative value satisfies
  rw [failure] at found
  cases found

/-- Every non-current variable in the source region has a prefix assignment. -/
def PrefixCovers (index : Nat) (knownValues : Nat → Option Int) (linear : Linear) : Prop :=
  ∀ entry ∈ linear.coefficients, entry.1 = index ∨ ∃ value, knownValues entry.1 = some value

/-- Prefix substitution leaves only the current variable. -/
theorem substitute_only (index : Nat) (knownValues : Nat → Option Int) (linear : Linear)
    (covers : PrefixCovers index knownValues linear) : Only index (substitute knownValues linear) := by
  intro entry member
  have original := List.mem_filter.mp member
  rcases covers entry original.1 with current | assigned
  · exact current
  · obtain ⟨value, assigned⟩ := assigned
    simp [assigned] at original

/-- The source substitutes the prefix before it extracts each interval. -/
def intervalWithPrefix (index : Nat) (knownValues : Nat → Option Int) (forms : List Linear) : Option (Int × Int) :=
  interval index (forms.map (substitute knownValues))

/-- Successful source prefix extraction has exact original-region semantics. -/
theorem intervalWithPrefix_correct (assignment : Nat → Int) (index : Nat) (knownValues : Nat → Option Int)
    (forms : List Linear) (valid : ∀ form ∈ forms, Valid form)
    (covers : ∀ form ∈ forms, PrefixCovers index knownValues form)
    (low high value : Int) (success : intervalWithPrefix index knownValues forms = some (low, high)) :
    (∀ form ∈ forms, 0 ≤ evaluate (override knownValues (LatticeBound.update assignment index value)) form) ↔
      low ≤ value ∧ value ≤ high := by
  have result := interval_correct assignment index (forms.map (substitute knownValues))
    (by
      intro form member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact substitute_valid knownValues original (valid original originalMember))
    (by
      intro form member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact substitute_only index knownValues original (covers original originalMember)) low high value success
  simpa only [List.forall_mem_map, evaluate_substitute] using result

/-- Substitution leaves the selected aggregate coefficient when that variable is unassigned. -/
theorem coefficient_substitute (knownValues : Nat → Option Int) (index : Nat)
    (unassigned : knownValues index = none) (coefficients : List (Nat × Int)) :
    Sparse.coefficient (coefficients.filter fun entry => (knownValues entry.1).isNone) index =
      Sparse.coefficient coefficients index := by
  induction coefficients with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, coefficient⟩
    by_cases same : other = index
    · subst other
      simp only [List.filter_cons, unassigned, Option.isNone_none, ↓reduceIte, Sparse.coefficient, ih]
    · cases found : knownValues other <;>
        simp [found, Sparse.coefficient, same, ih]

/-- Prefix substitution preserves the current source lookup exactly. -/
theorem coefficientOf_substitute (knownValues : Nat → Option Int) (index : Nat)
    (unassigned : knownValues index = none) (linear : Linear) (valid : Valid linear) :
    LatticeBound.coefficientOf index (substitute knownValues linear) = LatticeBound.coefficientOf index linear := by
  unfold LatticeBound.coefficientOf
  rw [Sparse.valueAtSize_correct _ (substitute_valid knownValues linear valid).1,
    Sparse.valueAtSize_correct _ valid.1]
  exact coefficient_substitute knownValues index unassigned linear.coefficients

/-- Failed source prefix extraction cannot omit any solution when both original bounds exist. -/
theorem intervalWithPrefix_none (assignment : Nat → Int) (index : Nat) (knownValues : Nat → Option Int)
    (unassigned : knownValues index = none) (forms : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (covers : ∀ form ∈ forms, PrefixCovers index knownValues form)
    (positive : ∃ form ∈ forms, 0 < LatticeBound.coefficientOf index form)
    (negative : ∃ form ∈ forms, LatticeBound.coefficientOf index form < 0)
    (failure : intervalWithPrefix index knownValues forms = none) :
    ∀ value, ¬ (∀ form ∈ forms,
      0 ≤ evaluate (override knownValues (LatticeBound.update assignment index value)) form) := by
  have convertedValid : ∀ form ∈ forms.map (substitute knownValues), Valid form := by
    intro form member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact substitute_valid knownValues original (valid original originalMember)
  have convertedOnly : ∀ form ∈ forms.map (substitute knownValues), Only index form := by
    intro form member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact substitute_only index knownValues original (covers original originalMember)
  have convertedPositive : ∃ form ∈ forms.map (substitute knownValues), 0 < LatticeBound.coefficientOf index form := by
    obtain ⟨form, member, positive⟩ := positive
    refine ⟨substitute knownValues form, List.mem_map.mpr ⟨form, member, rfl⟩, ?_⟩
    rw [coefficientOf_substitute knownValues index unassigned form (valid form member)]
    exact positive
  have convertedNegative : ∃ form ∈ forms.map (substitute knownValues), LatticeBound.coefficientOf index form < 0 := by
    obtain ⟨form, member, negative⟩ := negative
    refine ⟨substitute knownValues form, List.mem_map.mpr ⟨form, member, rfl⟩, ?_⟩
    rw [coefficientOf_substitute knownValues index unassigned form (valid form member)]
    exact negative
  intro value satisfies
  apply interval_none assignment index (forms.map (substitute knownValues)) convertedValid convertedOnly
    convertedPositive convertedNegative failure value
  simpa only [List.forall_mem_map, evaluate_substitute] using satisfies

end MicroCFTA.LatticeInterval
