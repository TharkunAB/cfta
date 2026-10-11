import MicroCFTA.Symbolic

/-!
# Union indicators with unrestricted intermediate signed coefficients

Only original alternatives need Boolean membership values. Every generated
intersection uses the proved multiplicative numeric interpretation. This
avoids assuming that arbitrary source edge records contain valid indicators.
-/
namespace MicroCFTA.SignedUnion
open Symbolic
open Lattice (indicator)

/-- A numeric interpretation sends graph intersection to integer multiplication. -/
def ExactProduct (value : Key → Int) (meet : Key → Key → Option Key) : Prop :=
  ∀ left right, (match meet left right with | none => 0 | some common => value common) = value left * value right

/-- The signed intersection loop computes the negated product with its current sum. -/
theorem overlaps_product (value : Key → Int) (meet : Key → Key → Option Key)
    (exact : ExactProduct value meet) (key : Key) (entries : Coefficients Key) :
    weighted value (overlaps meet key entries) = -(value key * weighted value entries) := by
  induction entries with
  | nil => simp [overlaps, weighted]
  | cons entry rest ih =>
      rcases entry with ⟨other, coefficient⟩
      have product := exact key other
      cases found : meet key other with
      | none =>
          simp only [found] at product
          simp only [overlaps, List.filterMap_cons, found, Option.map_none, weighted] at *
          rw [ih]
          grind
      | some common =>
          simp only [found] at product
          simp only [overlaps, List.filterMap_cons, found, Option.map_some, weighted] at *
          rw [ih, product]
          grind

/-- One insertion has the exact union polynomial, without restrictions on stored keys. -/
theorem add_product [DecidableEq Key] (value : Key → Int) (meet : Key → Key → Option Key)
    (exact : ExactProduct value meet) (entries : Coefficients Key) (key : Key) :
    weighted value (addAlternative meet entries key) =
      weighted value entries + value key - value key * weighted value entries := by
  simp only [addAlternative, weighted_trim, weighted_insert, weighted_collect, weighted_append,
    overlaps_product value meet exact, Int.one_mul]
  omega

/-- Boolean original alternatives yield exact union membership through arbitrary intersections. -/
theorem union_indicator [DecidableEq Key] (value : Key → Int) (member : Key → Bool)
    (meet : Key → Key → Option Key) (exact : ExactProduct value meet) (keys : List Key)
    (originals : ∀ key ∈ keys, value key = indicator (member key)) :
    weighted value (unionCoefficients meet keys) = indicator (keys.any member) := by
  have loop : ∀ rest : List Key, (∀ key ∈ rest, value key = indicator (member key)) →
      ∀ (entries : Coefficients Key) (seen : Bool), weighted value entries = indicator seen →
      weighted value (rest.foldl (addAlternative meet) entries) = indicator (seen || rest.any member) := by
    intro rest
    induction rest with
    | nil => intro _ entries seen previous; simpa using previous
    | cons key rest ih =>
        intro originals entries seen previous
        have step : weighted value (addAlternative meet entries key) = indicator (seen || member key) := by
          rw [add_product value meet exact, previous, originals key (by simp), Lattice.indicator_or]
          grind
        simp only [List.foldl_cons]
        rw [ih (fun key present => originals key (by simp [present])) _ _ step]
        simp [Bool.or_assoc]
  simpa [unionCoefficients, indicator] using loop keys originals [] false rfl

end MicroCFTA.SignedUnion
