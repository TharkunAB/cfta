import MicroCFTA.Sparse
import MicroCFTA.SourceSizedGroupedIndex

/-!
# The source minimum seed for finite sparse counts

This function follows `Ranked/Internal/Size.hs:839-841`. `none` represents
`NoFiniteMember`. A known minimum supplies the first size. The remaining
entries are the literal source suffix, with sizes at most the minimum removed.

The arithmetic lemmas use finite natural count series. The class lower bound
is an internal input to the count adapter. A computed minimum must establish
it. These lemmas do not prove productivity of a lazy infinite series or a
machine size bound.
-/
namespace MicroCFTA.SourceSizedFromMinimum

open Sparse (Series Ordered coefficient valueAtSize)

/-- Insert the computed minimum and retain the source suffix. -/
def fromMinimum : Option Nat → Series Nat → Series Nat
  | none, _ => []
  | some minimum, series =>
      (minimum, valueAtSize series minimum) ::
        series.dropWhile (fun entry => decide (entry.1 ≤ minimum))

/-- Every retained entry lies strictly above the inserted size. -/
theorem tail_above (series : Series Nat) (ordered : Ordered series) (minimum : Nat) :
    ∀ entry ∈ series.dropWhile (fun entry => decide (entry.1 ≤ minimum)),
      minimum < entry.1 := by
  revert ordered
  induction series with
  | nil => simp
  | cons first rest ih =>
    intro ordered entry member
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    by_cases skipped : first.1 ≤ minimum
    · apply ih tailOrdered entry
      simpa [List.dropWhile_cons, skipped] using member
    · have included : entry ∈ first :: rest := by
        simpa [List.dropWhile_cons, skipped] using member
      rcases List.mem_cons.mp included with equal | later
      · subst entry
        omega
      · have before := headBefore entry later
        omega

/-- The seed and retained suffix have strictly increasing sizes. -/
theorem ordered (minimum : Option Nat) (series : Series Nat) (input : Ordered series) :
    Ordered (fromMinimum minimum series) := by
  cases minimum with
  | none => exact List.Pairwise.nil
  | some minimum =>
    apply List.pairwise_cons.mpr
    exact ⟨tail_above series input minimum,
      List.Pairwise.sublist (List.dropWhile_sublist _) input⟩

/-- Removing the low prefix preserves each coefficient above the cut. -/
theorem coefficient_tail_above (series : Series Nat) (minimum wanted : Nat)
    (above : minimum < wanted) :
    coefficient (series.dropWhile (fun entry => decide (entry.1 ≤ minimum))) wanted =
      coefficient series wanted := by
  induction series with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨size, value⟩
    by_cases skipped : size ≤ minimum
    · have different : size ≠ wanted := by omega
      simpa [List.dropWhile_cons, skipped, coefficient, different] using ih
    · simp [skipped]

/-- The retained suffix contributes zero at or below the cut. -/
theorem coefficient_tail_below (series : Series Nat) (input : Ordered series)
    (minimum wanted : Nat) (below : wanted ≤ minimum) :
    coefficient (series.dropWhile (fun entry => decide (entry.1 ≤ minimum))) wanted = 0 := by
  apply Sparse.coefficient_below
  intro entry member
  have above := tail_above series input minimum entry member
  omega

/-- A known lower bound preserves every coefficient, including the seed. -/
theorem coefficient_some (series : Series Nat) (input : Ordered series) (minimum : Nat)
    (lower : ∀ wanted < minimum, coefficient series wanted = 0) (wanted : Nat) :
    coefficient (fromMinimum (some minimum) series) wanted = coefficient series wanted := by
  by_cases below : wanted < minimum
  · have different : minimum ≠ wanted := by omega
    have tailZero := coefficient_tail_below series input minimum wanted (by omega)
    simp only [fromMinimum, coefficient, different, ite_false, tailZero, Nat.zero_add]
    exact (lower wanted below).symm
  · by_cases equal : wanted = minimum
    · subst wanted
      have tailZero := coefficient_tail_below series input minimum minimum (Nat.le_refl _)
      simpa [fromMinimum, coefficient, tailZero] using
        Sparse.valueAtSize_correct series input minimum
    · have above : minimum < wanted := by omega
      have different : minimum ≠ wanted := by omega
      simpa only [fromMinimum, coefficient, different, ite_false, Nat.zero_add] using
        coefficient_tail_above series minimum wanted above

/-- No finite member preserves the coefficients of an identically zero series. -/
theorem coefficient_none (series : Series Nat)
    (empty : ∀ wanted, coefficient series wanted = 0) (wanted : Nat) :
    coefficient (fromMinimum none series) wanted = coefficient series wanted := by
  exact (empty wanted).symm

/-- Ordered sparse lookup retains all counts after insertion of the minimum. -/
theorem lookup_some (series : Series Nat) (input : Ordered series) (minimum : Nat)
    (lower : ∀ wanted < minimum, coefficient series wanted = 0) (wanted : Nat) :
    valueAtSize (fromMinimum (some minimum) series) wanted = valueAtSize series wanted := by
  rw [Sparse.valueAtSize_correct _ (ordered _ series input),
    coefficient_some series input minimum lower, Sparse.valueAtSize_correct series input]

/-- No finite member retains zero lookup results. -/
theorem lookup_none (series : Series Nat) (input : Ordered series)
    (empty : ∀ wanted, coefficient series wanted = 0) (wanted : Nat) :
    valueAtSize (fromMinimum none series) wanted = valueAtSize series wanted := by
  rw [Sparse.valueAtSize_correct _ (ordered _ series input),
    coefficient_none series empty, Sparse.valueAtSize_correct series input]

/-- Reading the first size does not require a coefficient equation. -/
theorem first_size (minimum : Nat) (series : Series Nat) :
    ((fromMinimum (some minimum) series).head?).map Prod.fst = some minimum := rfl

/-- The source retains the original suffix without changing its entries. -/
theorem tail_readback (minimum : Nat) (series : Series Nat) :
    (fromMinimum (some minimum) series).tail =
      series.dropWhile (fun entry => decide (entry.1 ≤ minimum)) := rfl

/-- The discarded read prefix and the retained suffix reconstruct the input. -/
theorem prefix_decomposition (minimum : Nat) (series : Series Nat) :
    series.takeWhile (fun entry => decide (entry.1 ≤ minimum)) ++
        (fromMinimum (some minimum) series).tail = series := by
  exact List.takeWhile_append_dropWhile

/-- The source seed replaces a singleton, including at size zero. -/
theorem singleton (minimum value : Nat) :
    fromMinimum (some minimum) [(minimum, value)] = [(minimum, value)] := by
  simp [fromMinimum, valueAtSize]

/-- A derived class lower bound connects the source seed to the count field. -/
theorem counts_of_correct {Value : Type} (series : Series Nat) (input : Ordered series)
    (index : RecursiveJoinFields.ValueIndex Value) (classes : Nat → List Value)
    (correct : SourceSizedGroupedIndex.Correct index classes)
    (stored : ∀ wanted, coefficient series wanted = index.counts wanted)
    (minimum : Nat) (lower : ∀ wanted < minimum, classes wanted = []) (wanted : Nat) :
    valueAtSize (fromMinimum (some minimum) series) wanted = index.counts wanted ∧
      valueAtSize (fromMinimum (some minimum) series) wanted = (classes wanted).length := by
  have coefficientLower : ∀ size < minimum, coefficient series size = 0 := by
    intro size below
    rw [stored size, correct.counts size, lower size below]
    rfl
  have count : valueAtSize (fromMinimum (some minimum) series) wanted = index.counts wanted := by
    rw [Sparse.valueAtSize_correct _ (ordered _ series input),
      coefficient_some series input minimum coefficientLower, stored wanted]
  exact ⟨count, count.trans (correct.counts wanted)⟩

end MicroCFTA.SourceSizedFromMinimum
