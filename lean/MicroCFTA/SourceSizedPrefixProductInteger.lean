import MicroCFTA.SourceSizedPrefixProductRank
import Init.Data.List.Nat.Range

/-!
# Integer allocation correspondence

The interval uses the source ascending Integer order.
The minimum table has Nat values. Successful lookups are embedded into Int.
The actual minimumSizes producer and the native row reifier remain separate.
-/
namespace MicroCFTA.SourceSizedPrefixProductInteger
open SourceSizedPrefixProductRank
variable {State : Type}

/-- Enumerate the closed Integer interval in ascending order. -/
def integerInterval (lower upper : Int) : List Int :=
  (List.range (upper - lower + 1).toNat).map fun (offset : Nat) => lower + (offset : Int)

/-- The interval retains one position for each Integer in its closed bounds. -/
theorem integerInterval_length (lower upper : Int) :
    (integerInterval lower upper).length = (upper - lower + 1).toNat := by
  simp [integerInterval]

/-- Interval membership is exactly the source lower and upper test. -/
theorem integerInterval_mem (lower upper value : Int) :
    value ∈ integerInterval lower upper ↔ lower ≤ value ∧ value ≤ upper := by
  simp only [integerInterval, List.mem_map]
  constructor
  · rintro ⟨offset, within, rfl⟩
    have bounded := List.mem_range.mp within
    omega
  · intro bounded
    refine ⟨(value - lower).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

private theorem filter_all {α : Type} (predicate : α → Bool) (values : List α)
    (witness : ∀ value ∈ values, predicate value = true) : values.filter predicate = values := by
  exact List.filter_eq_self.mpr witness

private theorem filter_none {α : Type} (predicate : α → Bool) (values : List α)
    (witness : ∀ value ∈ values, predicate value = false) : values.filter predicate = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro value member
  simp [witness value member]

private theorem range_split (cut total : Nat) (fits : cut ≤ total) :
    List.range total = List.range cut ++ List.range' cut (total - cut) := by
  have full : cut + (total - cut) = total := by omega
  simpa only [List.range_eq_range', Nat.zero_add, full] using
    (List.range'_append_1 (s := 0) (m := cut) (n := total - cut)).symm

private theorem range_filter_window (limit lower upper : Nat) (within : upper < limit) :
    (List.range limit).filter (fun value => decide (lower ≤ value ∧ value ≤ upper)) =
      List.range' lower (upper + 1 - lower) := by
  by_cases room : lower ≤ upper + 1
  · have belowWindow :
        (List.range lower).filter (fun value => decide (lower ≤ value ∧ value ≤ upper)) = [] :=
      filter_none _ _ (by
        intro value member
        have below := List.mem_range.mp member
        have rejected : ¬(lower ≤ value ∧ value ≤ upper) := by omega
        simp [rejected])
    have middle :
        (List.range' lower (upper + 1 - lower)).filter
          (fun value => decide (lower ≤ value ∧ value ≤ upper)) =
            List.range' lower (upper + 1 - lower) :=
      filter_all _ _ (by
        intro value member
        have bounds := List.mem_range'_1.mp member
        have accepted : lower ≤ value ∧ value ≤ upper := by omega
        simp [accepted])
    have suffix :
        (List.range' (upper + 1) (limit - (upper + 1))).filter
          (fun value => decide (lower ≤ value ∧ value ≤ upper)) = [] :=
      filter_none _ _ (by
        intro value member
        have bounds := List.mem_range'_1.mp member
        have rejected : ¬(lower ≤ value ∧ value ≤ upper) := by omega
        simp [rejected])
    rw [range_split (upper + 1) limit (by omega), range_split lower (upper + 1) room,
      List.filter_append, List.filter_append, belowWindow, middle, suffix]
    simp
  · have empty : upper + 1 - lower = 0 := by omega
    have rejected :
        (List.range limit).filter (fun value => decide (lower ≤ value ∧ value ≤ upper)) = [] :=
      filter_none _ _ (by
        intro value _member
        have impossible : ¬(lower ≤ value ∧ value ≤ upper) := by omega
        simp [impossible])
    simpa [empty] using rejected

private theorem integerInterval_nat (lower upper : Nat) :
    integerInterval (lower : Int) (upper : Int) =
      (List.range' lower (upper + 1 - lower)).map Int.ofNat := by
  have count : ((upper : Int) - (lower : Int) + 1).toNat = upper + 1 - lower := by omega
  simp only [integerInterval, count, List.range'_eq_map_range, List.map_map]
  rfl

/-- The literal Integer interval equals the filtered Nat loop as an ordered list. -/
theorem integerInterval_embedded (smallest total reserved : Nat) :
    integerInterval (smallest : Int) ((total : Int) - (reserved : Int)) =
      ((List.range (total + 1)).filter fun first =>
        decide (smallest ≤ first ∧ first + reserved ≤ total)).map Int.ofNat := by
  by_cases fits : reserved ≤ total
  · have upper : (total : Int) - (reserved : Int) = ((total - reserved : Nat) : Int) := by omega
    have predicates :
        (fun first : Nat => decide (smallest ≤ first ∧ first + reserved ≤ total)) =
        (fun first : Nat => decide (smallest ≤ first ∧ first ≤ total - reserved)) := by
      funext first
      by_cases accepted : smallest ≤ first ∧ first + reserved ≤ total
      · have other : smallest ≤ first ∧ first ≤ total - reserved := by omega
        simp [accepted, other]
      · have other : ¬(smallest ≤ first ∧ first ≤ total - reserved) := by omega
        simp [accepted, other]
    rw [upper, integerInterval_nat, predicates,
      range_filter_window (total + 1) smallest (total - reserved) (by omega)]
  · have count : ((total : Int) - (reserved : Int) - (smallest : Int) + 1).toNat = 0 := by omega
    have rejected :
        (List.range (total + 1)).filter
          (fun first => decide (smallest ≤ first ∧ first + reserved ≤ total)) = [] :=
      filter_none _ _ (by
        intro first _member
        have impossible : ¬(smallest ≤ first ∧ first + reserved ≤ total) := by omega
        simp [impossible])
    rw [rejected]
    simp [integerInterval, count]

private theorem flatMap_filter {α β : Type} (predicate : α → Bool) (worker : α → List β)
    (values : List α) :
    (values.filter predicate).flatMap worker =
      values.flatMap (fun value => if predicate value then worker value else []) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      cases answer : predicate value <;> simp [answer, ih]

private theorem sum_cast (values : List Nat) :
    (values.map Int.ofNat).sum = (values.sum : Int) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      change (value : Int) + (rest.sum : Int) = ((value + rest.sum : Nat) : Int)
      omega

/-- Run source Integer splits with the embedded original Nat minimum table. -/
def splits (minimum : State → Option Nat) : List State → Int → List (List Int)
  | [], total => if total = 0 then [[]] else []
  | current :: rest, total =>
      match minimum current, rest.mapM minimum with
      | some smallest, some others =>
          (integerInterval (smallest : Int) (total - (others.map Int.ofNat).sum)).flatMap fun first =>
            (splits minimum rest (total - first)).map fun tail => first :: tail
      | _, _ => []

/-- A negative source total generates no allocation under an embedded Nat table. -/
theorem splits_negative (minimum : State → Option Nat) (states : List State)
    (total : Int) (negative : total < 0) : splits minimum states total = [] := by
  cases states with
  | nil =>
      have nonzero : total ≠ 0 := by omega
      simp [splits, nonzero]
  | cons current rest =>
      cases currentMinimum : minimum current with
      | none => simp [splits, currentMinimum]
      | some smallest =>
        cases restMinimum : rest.mapM minimum with
        | none => simp [splits, currentMinimum, restMinimum]
        | some others =>
          have count : (total - (others.sum : Int) - (smallest : Int) + 1).toNat = 0 := by omega
          simp [splits, currentMinimum, restMinimum, sum_cast, integerInterval, count]

/-- Read the embedded budget list from an ordered Nat allocation. -/
def castParts (allocation : List (State × Nat)) : List Int :=
  allocation.map fun entry => (entry.2 : Int)

/-- Literal Integer splits and the Nat allocation core have the same ordered output. -/
theorem splits_embedded (minimum : State → Option Nat) (states : List State) (total : Nat) :
    splits minimum states (total : Int) =
      (allocations minimum states total).map castParts := by
  induction states generalizing total with
  | nil =>
      by_cases zero : total = 0
      · subst total
        rfl
      · simp [splits, allocations, zero]
  | cons current rest ih =>
      cases currentMinimum : minimum current with
      | none => simp [splits, allocations, currentMinimum]
      | some smallest =>
        cases restMinimum : rest.mapM minimum with
        | none => simp [splits, allocations, currentMinimum, restMinimum]
        | some others =>
          simp only [splits, allocations, currentMinimum, restMinimum]
          rw [sum_cast, integerInterval_embedded, List.flatMap_map, flatMap_filter,
            List.map_flatMap]
          apply congrArg (fun worker : Nat → List (List Int) =>
            (List.range (total + 1)).flatMap worker)
          funext first
          by_cases permitted : smallest ≤ first ∧ first + others.sum ≤ total
          · have sub : (total : Int) - (first : Int) = ((total - first : Nat) : Int) := by omega
            simp [permitted, sub, ih (total - first), castParts, List.map_map]
          · simp [permitted]

end MicroCFTA.SourceSizedPrefixProductInteger
