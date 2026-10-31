import MicroCFTA.SourceSizedPrefixProductInteger
import Init.Data.List.TakeDrop

/-!
# The source numeric equality-size filter

The input is the current output view of equalities, not the full constraint.
Signed path indexes retain the source negative-index branch.
The actual equalities and minimumSizes producers remain separate.
-/
namespace MicroCFTA.SourceSizedPrefixEqualSizes
open SourceSizedPrefixProductRank SourceSizedPrefixProductInteger
variable {State : Type}

/-- The source equality view. None denotes EqContradiction. -/
abbrev EqualityView := Option (List (List (List Int)))

/-- Keep only the singleton-child paths, in their current source list order. -/
def directChildren (paths : List (List Int)) : List Int :=
  paths.filterMap fun path => match path with
    | [child] => some child
    | _ => none

/-- Read a source child size. Negative and out-of-range indexes give None. -/
def sizeOf {α : Type} (parts : List α) (child : Int) : Option α :=
  if 0 ≤ child then (parts.drop child.toNat).head? else none

private theorem sizeOf_map {α β : Type} (function : α → β) (parts : List α) (child : Int) :
    sizeOf (parts.map function) child = (sizeOf parts child).map function := by
  by_cases nonnegative : 0 ≤ child
  · simp only [sizeOf, ite_eq_left nonnegative, ← List.map_drop, List.head?_map]
  · simp [sizeOf, nonnegative]

/-- Traverse the selected source child indexes with the source Maybe behavior. -/
def readSizes {α : Type} (parts : List α) : List Int → Option (List α)
  | [] => some []
  | child :: rest => do
      let first ← sizeOf parts child
      let others ← readSizes parts rest
      pure (first :: others)

private theorem readSizes_map {α β : Type} (function : α → β) (parts : List α)
    (children : List Int) :
    readSizes (parts.map function) children = (readSizes parts children).map (List.map function) := by
  induction children with
  | nil => rfl
  | cons child rest ih =>
      simp only [readSizes, sizeOf_map, ih]
      cases found : sizeOf parts child <;> cases remaining : readSizes parts rest <;> rfl

/-- Test the source Maybe result. Empty selected classes pass. -/
def allSame {α : Type} [DecidableEq α] : Option (List α) → Bool
  | none => false
  | some [] => true
  | some (first :: rest) => rest.all fun value => decide (value = first)

private theorem allSame_cast (values : Option (List Nat)) :
    allSame (values.map (List.map Int.ofNat)) = allSame values := by
  cases values with
  | none => rfl
  | some values =>
      cases values with
      | nil => rfl
      | cons first rest => simp [allSame, List.all_map, Function.comp_def, Int.ofNat_inj]

/-- Run the source prefilter on the current equality view. -/
def equalSizes {α : Type} [DecidableEq α] (equalities : EqualityView) (parts : List α) : Bool :=
  match equalities with
  | none => true
  | some classes => classes.all fun paths => allSame (readSizes parts (directChildren paths))

/-- The contradiction case passes this numeric prefilter, as in the source. -/
theorem equalSizes_contradiction {α : Type} [DecidableEq α] (parts : List α) :
    equalSizes none parts = true := rfl

/-- Embedding the current Nat parts preserves the exact source filter result. -/
theorem equalSizes_cast (equalities : EqualityView) (parts : List Nat) :
    equalSizes equalities (parts.map Int.ofNat) = equalSizes equalities parts := by
  cases equalities with
  | none => rfl
  | some classes =>
      unfold equalSizes
      apply congrArg (fun test : List (List Int) → Bool => classes.all test)
      funext paths
      rw [readSizes_map]
      exact allSame_cast (readSizes parts (directChildren paths))

/-- Filtered literal splits retain the Nat core's exact order and multiplicity. -/
theorem filtered_splits_embedded (minimum : State → Option Nat) (states : List State)
    (total : Nat) (equalities : EqualityView) :
    (splits minimum states (total : Int)).filter (equalSizes equalities) =
      ((allocations minimum states total).filter fun allocation =>
        equalSizes equalities (allocation.map Prod.snd)).map castParts := by
  rw [splits_embedded]
  generalize allocations minimum states total = generated
  induction generated with
  | nil => rfl
  | cons allocation rest ih =>
      have same : equalSizes equalities (castParts allocation) =
          equalSizes equalities (allocation.map Prod.snd) := by
        simpa [castParts, List.map_map, Function.comp_def] using equalSizes_cast equalities (allocation.map Prod.snd)
      cases kept : equalSizes equalities (allocation.map Prod.snd) <;> simp [same, kept, ih]

/-- Preserve negative Integer totals without truncating them into a zero allocation. -/
theorem filtered_splits_integer (minimum : State → Option Nat) (states : List State)
    (total : Int) (equalities : EqualityView) :
    (splits minimum states total).filter (equalSizes equalities) =
      if total < 0 then [] else
        ((allocations minimum states total.toNat).filter fun allocation =>
          equalSizes equalities (allocation.map Prod.snd)).map castParts := by
  by_cases negative : total < 0
  · rw [splits_negative minimum states total negative]
    simp [negative]
  · have embedded : (total.toNat : Int) = total := by omega
    simpa [negative, embedded] using filtered_splits_embedded minimum states total.toNat equalities

end MicroCFTA.SourceSizedPrefixEqualSizes
