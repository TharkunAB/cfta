import MicroCFTA.SourceSizedGroupedSparseMinimum
import MicroCFTA.SourceSizedGroupedPublicQueries

/-!
# Signed Integer lookup in finite source count series

The lookup follows Size.hs valueAtSize. It skips smaller stored sizes,
then compares the first remaining size with the original signed request.
Stored sizes here are natural numbers, embedded in Integer. Negative
requests return zero without a fromTable size guard.

For nonnegative requests, this loop equals the checked natural sparse
lookup. Projection through size.toNat at all signed sizes requires a zero
coefficient at size zero. Internal constant indexes do not have that fact.
Actual prepared state series do have it, from the checked grouped classes.

The final adapter reads the actual finite sparse unfolding with the shared
computed minimum. It does not establish lazy infinite-series productivity,
sharing, native map storage, machine conversions, or total execution cost.
-/
namespace MicroCFTA.SourceSizedSparseSignedCounts
open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys

variable {State Symbol Formula : Type}

/-- Execute the source comparison and equality loop at the original Integer size. -/
def valueAtSize : Sparse.Series Nat → Int → Nat
  | [], _ => 0
  | (size, value) :: rest, wanted =>
      if (size : Int) < wanted then valueAtSize rest wanted
      else if (size : Int) = wanted then value else 0

/-- The recursive loop is the literal source dropWhile followed by head equality. -/
theorem valueAtSize_dropWhile (series : Sparse.Series Nat) (wanted : Int) :
    valueAtSize series wanted =
      match series.dropWhile (fun entry => decide ((entry.1 : Int) < wanted)) with
      | [] => 0
      | (found, value) :: _ => if (found : Int) = wanted then value else 0 := by
  induction series with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨size, value⟩
      by_cases smaller : (size : Int) < wanted
      · simpa only [valueAtSize, smaller, ite_true, List.dropWhile_cons, decide_true] using ih
      · simp [valueAtSize, smaller]

/-- Natural request sizes retain the exact existing sparse comparison loop. -/
theorem valueAtSize_nat (series : Sparse.Series Nat) (wanted : Nat) :
    valueAtSize series (wanted : Int) = Sparse.valueAtSize series wanted := by
  induction series with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨size, value⟩
      have smaller : ((size : Int) < (wanted : Int)) ↔ size < wanted := by omega
      have same : ((size : Int) = (wanted : Int)) ↔ size = wanted := by omega
      simp only [valueAtSize, Sparse.valueAtSize, smaller, same, ih]

/-- Nonnegative signed requests have the same natural sparse observation. -/
theorem valueAtSize_nonnegative (series : Sparse.Series Nat) (wanted : Int) (nonnegative : 0 ≤ wanted) :
    valueAtSize series wanted = Sparse.valueAtSize series wanted.toNat := by
  have actual := valueAtSize_nat series wanted.toNat
  rw [Int.toNat_of_nonneg nonnegative] at actual
  exact actual

/-- A negative request stops before the first nonnegative stored size and returns zero. -/
theorem valueAtSize_negative (series : Sparse.Series Nat) (wanted : Int) (negative : wanted < 0) :
    valueAtSize series wanted = 0 := by
  cases series with
  | nil => rfl
  | cons entry rest =>
      rcases entry with ⟨size, value⟩
      have notSmaller : ¬(size : Int) < wanted := by omega
      have different : ¬(size : Int) = wanted := by omega
      simp only [valueAtSize, notSmaller, different, ite_false]

/-- Projection to natural sizes is valid when the series has no size-zero count. -/
theorem valueAtSize_toNat (series : Sparse.Series Nat) (zero : Sparse.valueAtSize series 0 = 0)
    (wanted : Int) : valueAtSize series wanted = Sparse.valueAtSize series wanted.toNat := by
  by_cases nonnegative : 0 ≤ wanted
  · exact valueAtSize_nonnegative series wanted nonnegative
  · have negative : wanted < 0 := by omega
    rw [valueAtSize_negative series wanted negative, Int.toNat_eq_zero.mpr (by omega), zero]

/-- The internal constant count shows why a general signed toNat projection is false. -/
theorem constant_negative_counterexample :
    valueAtSize [(0, 1)] (-1) = 0 ∧ Sparse.valueAtSize [(0, 1)] ((-1 : Int).toNat) = 1 := by
  decide

section Prepared

variable [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Every finite prepared state series has zero count at node size zero. -/
theorem evaluate_zero (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (fuel : Nat) (key : List State) :
    Sparse.valueAtSize
      (SourceSizedGroupedSparseMinimum.evaluate fuel
        (SourceSizedGroupedMinimumIndex.minimum original root output success) (lookup output) key).series 0 = 0 := by
  rw [SourceSizedGroupedSparseMinimum.evaluate_lookup]
  exact SourceSizedGroupedTableIndex.evaluate_zero_count fuel
    (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) key

/-- Actual prepared state series derive their signed projection condition internally. -/
theorem evaluate_signed_projection (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (fuel : Nat) (key : List State) (wanted : Int) :
    valueAtSize
      (SourceSizedGroupedSparseMinimum.evaluate fuel
        (SourceSizedGroupedMinimumIndex.minimum original root output success) (lookup output) key).series wanted =
      Sparse.valueAtSize
        (SourceSizedGroupedSparseMinimum.evaluate fuel
          (SourceSizedGroupedMinimumIndex.minimum original root output success) (lookup output) key).series wanted.toNat :=
  valueAtSize_toNat _ (evaluate_zero original root output success fuel key) wanted

/-- Read the finite source sparse series at the original signed request size. -/
def countAt (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (wanted : Int) : Nat :=
  valueAtSize
    (SourceSizedGroupedSparseMinimum.evaluate (wanted.toNat + 1)
      (SourceSizedGroupedMinimumIndex.minimum original root output success) (lookup output) key).series wanted

/-- Literal finite signed sparse lookup equals the independent public count projection. -/
theorem countAt_eq (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (wanted : Int) :
    countAt original root output success key wanted =
      SourceSizedGroupedPublicQueries.countAt original root output success key wanted := by
  unfold countAt
  rw [evaluate_signed_projection original root output success (wanted.toNat + 1) key wanted,
    SourceSizedGroupedSparseMinimum.requested_classes,
    SourceSizedGroupedPublicQueries.countAt_eq]

/-- Nonpositive prepared node-size counts are zero through the source sparse lookup. -/
theorem countAt_nonpositive (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (wanted : Int) (nonpositive : wanted ≤ 0) :
    countAt original root output success key wanted = 0 := by
  rw [countAt_eq]
  exact SourceSizedGroupedPublicQueries.countAt_nonpositive original root output success key wanted nonpositive

end Prepared
end MicroCFTA.SourceSizedSparseSignedCounts
