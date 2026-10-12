import MicroCFTA.Symbolic

/-!
# Work in the signed distinct-intersection union fold

Each new alternative intersects every retained coefficient key. Collection
and zero removal can reduce the next map, but they cannot prevent an
exponential upper bound. The cost here counts intersection requests. It
excludes the cost of each intersection, coefficient arithmetic, and maps.
-/
namespace MicroCFTA.SymbolicUnionCost
open Symbolic

/-- Coefficient insertion adds at most one key. -/
theorem insert_length [DecidableEq Key] (key : Key) (coefficient : Int) (entries : Coefficients Key) :
    (insertCoefficient key coefficient entries).length ≤ entries.length + 1 := by
  induction entries with
  | nil => simp [insertCoefficient]
  | cons entry rest ih =>
    rcases entry with ⟨other, value⟩
    simp only [insertCoefficient]
    split
    · simp
    · simpa using Nat.succ_le_succ ih

/-- Collection cannot create more keys than its input entries. -/
theorem collect_length [DecidableEq Key] (entries : Coefficients Key) :
    (collect entries).length ≤ entries.length := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
    have step := insert_length entry.1 entry.2 (collect rest)
    simp only [collect, List.foldr_cons] at step ih ⊢
    simp only [List.length_cons]
    omega

/-- A signed union step retains at most twice its old keys plus one. -/
theorem alternative_length [DecidableEq Key] (meet : Key → Key → Option Key)
    (entries : Coefficients Key) (key : Key) :
    (addAlternative meet entries key).length ≤ 2 * entries.length + 1 := by
  have trimBound := List.length_filter_le (fun entry : Key × Int => entry.2 != 0)
    (insertCoefficient key 1 (collect (entries ++ overlaps meet key entries)))
  have insertBound := insert_length key 1 (collect (entries ++ overlaps meet key entries))
  have collectBound := collect_length (entries ++ overlaps meet key entries)
  have overlapBound : (overlaps meet key entries).length ≤ entries.length := List.length_filterMap_le ..
  simp only [List.length_append] at collectBound
  change (addAlternative meet entries key).length ≤ _ at trimBound
  omega

/-- Run the source fold and count each attempted intersection with an existing key. -/
def measured [DecidableEq Key] (meet : Key → Key → Option Key) :
    List Key → Coefficients Key → Coefficients Key × Nat
  | [], entries => (entries, 0)
  | key :: rest, entries =>
    let result := measured meet rest (addAlternative meet entries key)
    (result.1, entries.length + result.2)

/-- Measuring intersections preserves the exact final coefficient list. -/
theorem measured_result [DecidableEq Key] (meet : Key → Key → Option Key)
    (keys : List Key) (entries : Coefficients Key) :
    (measured meet keys entries).1 = keys.foldl (addAlternative meet) entries := by
  induction keys generalizing entries with
  | nil => rfl
  | cons key rest ih => exact ih _

/-- The final signed map has at most one entry per nonempty alternative subset. -/
theorem retained_bound [DecidableEq Key] (meet : Key → Key → Option Key)
    (keys : List Key) (entries : Coefficients Key) :
    (measured meet keys entries).1.length + 1 ≤ 2 ^ keys.length * (entries.length + 1) := by
  induction keys generalizing entries with
  | nil => simp [measured]
  | cons key rest ih =>
    have recursive := ih (addAlternative meet entries key)
    have step := alternative_length meet entries key
    have grow : (addAlternative meet entries key).length + 1 ≤ 2 * (entries.length + 1) := by omega
    have scaled := Nat.mul_le_mul_left (2 ^ rest.length) grow
    simp only [measured, List.length_cons, Nat.pow_succ]
    calc
      _ ≤ 2 ^ rest.length * ((addAlternative meet entries key).length + 1) := recursive
      _ ≤ 2 ^ rest.length * (2 * (entries.length + 1)) := scaled
      _ = _ := by rw [Nat.mul_assoc]

/-- Intersection requests are bounded by the exponential number of alternative subsets. -/
theorem requests_bound [DecidableEq Key] (meet : Key → Key → Option Key)
    (keys : List Key) (entries : Coefficients Key) :
    (measured meet keys entries).2 ≤ (2 ^ keys.length - 1) * (entries.length + 1) := by
  induction keys generalizing entries with
  | nil => simp [measured]
  | cons key rest ih =>
    have recursive := ih (addAlternative meet entries key)
    have step := alternative_length meet entries key
    have grow : (addAlternative meet entries key).length + 1 ≤ 2 * (entries.length + 1) := by omega
    have scaled := Nat.mul_le_mul_left (2 ^ rest.length - 1) grow
    have positive : 0 < 2 ^ rest.length := Nat.two_pow_pos _
    have power : 2 ^ (rest.length + 1) - 1 = (2 ^ rest.length - 1) * 2 + 1 := by
      rw [Nat.pow_succ]
      omega
    simp only [measured, List.length_cons, power, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    omega

/-- Counting a union of `m` alternatives can retain at most `2^m - 1` distinct intersections. -/
theorem union_length_bound [DecidableEq Key] (meet : Key → Key → Option Key) (keys : List Key) :
    (unionCoefficients meet keys).length ≤ 2 ^ keys.length - 1 := by
  have result := retained_bound meet keys []
  rw [measured_result] at result
  simp only [List.length_nil, Nat.zero_add, Nat.mul_one] at result
  change (keys.foldl (addAlternative meet) []).length ≤ _
  omega

/-- The four-alternative source example reaches all fifteen nonempty subset intersections. -/
theorem four_alternatives_reach_bound :
    (unionCoefficients finiteMeet
      ([[1, 3, 5, 7, 9, 11, 13, 15], [2, 3, 6, 7, 10, 11, 14, 15],
        [4, 5, 6, 7, 12, 13, 14, 15], [8, 9, 10, 11, 12, 13, 14, 15]] : List (List Nat))).length =
      2 ^ 4 - 1 := exponential_intersections_example

end MicroCFTA.SymbolicUnionCost
