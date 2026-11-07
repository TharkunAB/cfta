import MicroCFTA.SourceSizedFromMinimum
import MicroCFTA.SourceSizedGroupedTableIndex

/-!
# Finite sparse storage for the source grouped count fields

`Stored` retains a finite count list and the minimum field. The operations
follow `Ranked/Internal/Size.hs`: constant, unchanged map, seeded pay, positive
scale, seeded sparse product, and the right fold of sparse sums. They do not
construct class lists or replace storage by a count function.

`Represents` relates this storage to the independently built count field.
Callback representation laws are internal induction inputs. Product and pay
derive their seed lower bounds from their operands. The row, state, and finite
table proofs execute these same storage operations.

The finite evaluator computes minima within each finite unfolding. It does
not identify those metadata with the shared table's global minimum pass.
Finite unfolding does not establish the productivity or sharing of the lazy
recursive table knot. Signed sizes, machine conversions, and execution costs
remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedSparseFields

open Language SourceSizedDecided
open Sparse (Series Ordered coefficient valueAtSize)
open RecursiveJoinFields (ValueIndex convolve)
open RecursiveJoinTyped (mapIndex productIndex)
open SourceSizedGroupedIndex (constantIndex emptyIndex payIndex scaleIndex choiceIndex)

variable {State Symbol Key Value Result Left Right : Type}

/-- The two stored fields used by the source count operations. -/
structure Stored where
  series : Series Nat
  minimum : Option Nat

/-- The minimum field excludes counts below it; none excludes every count. -/
def MinimumBound (minimum : Option Nat) (counts : Nat → Nat) : Prop :=
  match minimum with
  | none => ∀ size, counts size = 0
  | some lower => ∀ size < lower, counts size = 0

/-- Sparse storage agrees with an independently constructed count field. -/
structure Represents (stored : Stored) (index : ValueIndex Value) : Prop where
  ordered : Ordered stored.series
  counts : ∀ size, coefficient stored.series size = index.counts size
  minimum : MinimumBound stored.minimum index.counts

/-- Ordered source lookup reads the represented count field. -/
theorem Represents.lookup {stored : Stored} {index : ValueIndex Value}
    (represented : Represents stored index) (size : Nat) :
    valueAtSize stored.series size = index.counts size := by
  rw [Sparse.valueAtSize_correct stored.series represented.ordered, represented.counts]

/-- No finite member contributes no stored count. -/
def empty : Stored := ⟨[], none⟩

/-- The literal constant index stores its one member at size zero. -/
def constant : Stored := ⟨[(0, 1)], some 0⟩

/-- Apply the source minimum seed without changing the minimum metadata. -/
def seed (stored : Stored) : Stored :=
  ⟨SourceSizedFromMinimum.fromMinimum stored.minimum stored.series, stored.minimum⟩

/-- The minimum of a product adds the two present operand minima. -/
def productMinimum : Option Nat → Option Nat → Option Nat
  | some left, some right => some (left + right)
  | _, _ => none

/-- A source choice ignores alternatives with no finite member. -/
def choiceMinimum : Option Nat → Option Nat → Option Nat
  | none, right => right
  | left, none => left
  | some left, some right => some (min left right)

/-- Literal sparse multiplication precedes the computed product seed. -/
def product (left right : Stored) : Stored :=
  seed ⟨Sparse.mulSparse left.series right.series,
    productMinimum left.minimum right.minimum⟩

/-- Pay maps each stored size to its successor before the computed seed. -/
def pay (stored : Stored) : Stored :=
  seed ⟨stored.series.map (fun entry => (entry.1 + 1, entry.2)),
    stored.minimum.map (fun size => size + 1)⟩

/-- Source scaling maps stored sizes and retains their count values. -/
def scale (factor : Nat) (stored : Stored) : Stored :=
  ⟨stored.series.map (fun entry => (factor * entry.1, entry.2)),
    stored.minimum.map (fun size => factor * size)⟩

/-- Choice performs the literal source right fold of sparse addition. -/
def choice : List Stored → Stored
  | [] => empty
  | first :: rest =>
      let remaining := choice rest
      ⟨Sparse.addSparse first.series remaining.series,
        choiceMinimum first.minimum remaining.minimum⟩

private theorem sum_delta (items : List Nat) (distinct : items.Nodup)
    (key value : Nat) :
    (items.map (fun item => if item = key then value else 0)).sum =
      if key ∈ items then value else 0 := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨absent, remaining⟩ := List.nodup_cons.mp distinct
    by_cases same : first = key
    · subst first
      simp [ih remaining, absent]
    · simp [same, Ne.symm same, ih remaining]

private theorem sum_zero (items : List Nat) :
    (items.map (fun _ => (0 : Nat))).sum = 0 := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.zero_add]

private theorem convolve_add (first second right : Nat → Nat) (size : Nat) :
    convolve (fun part => first part + second part) right size =
      convolve first right size + convolve second right size := by
  have distribute (items : List Nat) :
      (items.map (fun part => (first part + second part) * right (size - part))).sum =
        (items.map (fun part => first part * right (size - part))).sum +
          (items.map (fun part => second part * right (size - part))).sum := by
    induction items with
    | nil => rfl
    | cons firstPart rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Nat.add_mul]
      omega
  exact distribute _

private theorem convolve_delta (key value : Nat) (right : Nat → Nat) (size : Nat) :
    convolve (fun part => if key = part then value else 0) right size =
      if key ≤ size then value * right (size - key) else 0 := by
  unfold convolve
  have pointwise (part : Nat) :
      (if key = part then value else 0) * right (size - part) =
        if part = key then value * right (size - key) else 0 := by
    by_cases same : part = key
    · simp [same]
    · simp [same, Ne.symm same]
  simp only [pointwise]
  rw [sum_delta _ List.nodup_range]
  simp only [List.mem_range, Nat.lt_succ_iff]

/-- Sparse Cartesian multiplication equals the independent size-split field. -/
theorem convolution_eq_convolve (left right : Series Nat) (size : Nat) :
    Sparse.convolution left right size =
      convolve (coefficient left) (coefficient right) size := by
  induction left with
  | nil => simp only [Sparse.convolution, coefficient, convolve, Nat.zero_mul, sum_zero]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    rw [Sparse.convolution, Sparse.coefficient_shiftScale, ih]
    change (if key ≤ size then value * coefficient right (size - key) else 0) +
        convolve (coefficient rest) (coefficient right) size =
      convolve (fun part => (if key = part then value else 0) + coefficient rest part)
        (coefficient right) size
    rw [convolve_add, convolve_delta]

private theorem product_minimum_bound (left right : Option Nat) (first second : Nat → Nat)
    (leftBound : MinimumBound left first) (rightBound : MinimumBound right second) :
    MinimumBound (productMinimum left right) (convolve first second) := by
  cases left with
  | none =>
    intro size
    have zero : ∀ wanted, first wanted = 0 := leftBound
    change convolve first second size = 0
    simp only [convolve, zero, Nat.zero_mul, sum_zero]
  | some left =>
    cases right with
    | none =>
      intro size
      have zero : ∀ wanted, second wanted = 0 := rightBound
      change convolve first second size = 0
      simp only [convolve, zero, Nat.mul_zero, sum_zero]
    | some right =>
      intro size below
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro value member
      obtain ⟨part, within, rfl⟩ := List.mem_map.mp member
      have inside : part ≤ size := Nat.le_of_lt_succ (List.mem_range.mp within)
      by_cases small : part < left
      · rw [leftBound part small]
        exact Nat.zero_mul _
      · have later : size - part < right := by
          change size < left + right at below
          omega
        rw [rightBound (size - part) later]
        exact Nat.mul_zero _

private theorem choice_minimum_bound (left right : Option Nat) (first second : Nat → Nat)
    (leftBound : MinimumBound left first) (rightBound : MinimumBound right second) :
    MinimumBound (choiceMinimum left right) (fun size => first size + second size) := by
  cases left <;> cases right <;> simp only [choiceMinimum, MinimumBound] at *
  · intro size
    rw [leftBound size, rightBound size]
  · intro size below
    rw [leftBound size, rightBound size below]
  · intro size below
    rw [leftBound size below, rightBound size]
  · intro size below
    rw [leftBound size (Nat.lt_of_lt_of_le below (Nat.min_le_left _ _)),
      rightBound size (Nat.lt_of_lt_of_le below (Nat.min_le_right _ _))]

private theorem shifted (series : Series Nat) :
    series.map (fun entry => (entry.1 + 1, entry.2)) = Sparse.shiftScale 1 1 series := by
  unfold Sparse.shiftScale
  apply List.map_congr_left
  intro entry _
  simp [Nat.add_comm]

private theorem scale_coefficient (factor : Nat) (positive : 0 < factor)
    (series : Series Nat) (size : Nat) :
    coefficient (series.map (fun entry => (factor * entry.1, entry.2))) size =
      if size % factor = 0 then coefficient series (size / factor) else 0 := by
  induction series with
  | nil => simp [coefficient]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [List.map_cons, coefficient, ih]
    by_cases divisible : size % factor = 0
    · have recovered : factor * (size / factor) = size :=
        Nat.mul_div_cancel_left' (Nat.dvd_of_mod_eq_zero divisible)
      have same : factor * key = size ↔ key = size / factor := by
        constructor
        · intro equal
          apply Nat.mul_left_cancel positive
          exact equal.trans recovered.symm
        · intro equal
          rw [equal]
          exact recovered
      simp only [divisible, ↓reduceIte, same]
    · have different : factor * key ≠ size := by
        intro equal
        apply divisible
        rw [← equal]
        simp
      simp [divisible, different]

/-- Empty storage represents the actual empty field projection. -/
theorem empty_represents : Represents empty (emptyIndex : ValueIndex Value) := by
  constructor
  · exact List.Pairwise.nil
  · intro size
    rfl
  · intro size
    rfl

/-- Constant storage represents the actual constant index count field. -/
theorem constant_represents (value : Value) : Represents constant (constantIndex value) := by
  constructor
  · simp [constant, Ordered]
  · intro size
    simp [constant, coefficient, constantIndex, eq_comm]
  · intro size below
    exact False.elim (Nat.not_lt_zero _ below)

/-- Mapping values leaves the same literal count storage and minimum. -/
theorem map_represents (transform : Value → Result) (stored : Stored) (index : ValueIndex Value)
    (represented : Represents stored index) : Represents stored (mapIndex transform index) := by
  exact ⟨represented.ordered, represented.counts, represented.minimum⟩

/-- A justified source seed preserves the independent count field. -/
theorem seed_represents (stored : Stored) (index : ValueIndex Value)
    (represented : Represents stored index) : Represents (seed stored) index := by
  constructor
  · exact SourceSizedFromMinimum.ordered _ _ represented.ordered
  · intro size
    cases minimum : stored.minimum with
    | none =>
      have bound : ∀ wanted, index.counts wanted = 0 := by
        simpa only [minimum, MinimumBound] using represented.minimum
      have emptyCounts : ∀ wanted, coefficient stored.series wanted = 0 := by
        intro wanted
        rw [represented.counts]
        exact bound wanted
      simpa only [seed, minimum] using
        (SourceSizedFromMinimum.coefficient_none stored.series emptyCounts size).trans
          (represented.counts size)
    | some lower =>
      have bound : ∀ wanted < lower, index.counts wanted = 0 := by
        simpa only [minimum, MinimumBound] using represented.minimum
      have lowerCounts : ∀ wanted < lower, coefficient stored.series wanted = 0 := by
        intro wanted below
        rw [represented.counts]
        exact bound wanted below
      simpa only [seed, minimum] using
        (SourceSizedFromMinimum.coefficient_some stored.series represented.ordered lower lowerCounts size).trans
          (represented.counts size)
  · exact represented.minimum

/-- Product derives its computed seed bound from the two operand minima. -/
theorem product_represents (combine : Left → Right → Result) (left right : Stored)
    (first : ValueIndex Left) (second : ValueIndex Right)
    (leftRep : Represents left first) (rightRep : Represents right second) :
    Represents (product left right) (productIndex combine first second) := by
  apply seed_represents
  constructor
  · exact Sparse.mulSparse_ordered _ _ leftRep.ordered rightRep.ordered
  · intro size
    rw [Sparse.coefficient_mulSparse, convolution_eq_convolve]
    have firstCounts : coefficient left.series = first.counts := funext leftRep.counts
    have secondCounts : coefficient right.series = second.counts := funext rightRep.counts
    rw [firstCounts, secondCounts]
    rfl
  · exact product_minimum_bound _ _ _ _ leftRep.minimum rightRep.minimum

/-- Pay derives its successor seed bound from the operand minimum. -/
theorem pay_represents (stored : Stored) (index : ValueIndex Value)
    (represented : Represents stored index) : Represents (pay stored) (payIndex index) := by
  apply seed_represents
  constructor
  · rw [shifted]
    exact Sparse.shiftScale_ordered _ _ _ represented.ordered
  · intro size
    rw [shifted, Sparse.coefficient_shiftScale]
    cases size with
    | zero => simp [payIndex]
    | succ size => simpa [payIndex] using represented.counts size
  · cases minimum : stored.minimum with
    | none =>
      intro size
      have emptyCounts : ∀ wanted, index.counts wanted = 0 := by
        simpa only [minimum, MinimumBound] using represented.minimum
      cases size <;> simp [payIndex, emptyCounts]
    | some lower =>
      intro size below
      have lowerCounts : ∀ wanted < lower, index.counts wanted = 0 := by
        simpa only [minimum, MinimumBound] using represented.minimum
      cases size with
      | zero => rfl
      | succ size =>
        exact lowerCounts size (by change size + 1 < lower + 1 at below; omega)

/-- Positive scaling preserves exact coefficients and the scaled minimum bound. -/
theorem scale_represents (factor : Nat) (positive : 0 < factor) (stored : Stored)
    (index : ValueIndex Value) (represented : Represents stored index) :
    Represents (scale factor stored) (scaleIndex factor index) := by
  have counts (size : Nat) : coefficient (scale factor stored).series size =
      (scaleIndex factor index).counts size := by
    change coefficient (stored.series.map (fun entry => (factor * entry.1, entry.2))) size =
      (scaleIndex factor index).counts size
    rw [scale_coefficient factor positive]
    by_cases one : factor = 1
    · subst factor
      simpa only [Nat.mod_one, Nat.div_one, scaleIndex, ↓reduceIte] using represented.counts size
    · simp only [scaleIndex, one, ↓reduceIte]
      split <;> simp [represented.counts]
  constructor
  · apply List.pairwise_map.mpr
    exact represented.ordered.imp (by
      intro first second before
      exact Nat.mul_lt_mul_of_pos_left before positive)
  · exact counts
  · change MinimumBound (stored.minimum.map (fun size => factor * size))
      (scaleIndex factor index).counts
    cases minimum : stored.minimum with
    | none =>
      intro size
      have emptyCounts : ∀ wanted, index.counts wanted = 0 := by
        simpa only [minimum, MinimumBound] using represented.minimum
      by_cases one : factor = 1
      · subst factor
        simpa only [scaleIndex, ↓reduceIte] using emptyCounts size
      · simp only [scaleIndex, one, ↓reduceIte]
        split
        · exact emptyCounts _
        · rfl
    | some lower =>
      intro size below
      have lowerCounts : ∀ wanted < lower, index.counts wanted = 0 := by
        simpa only [minimum, MinimumBound] using represented.minimum
      by_cases one : factor = 1
      · subst factor
        exact lowerCounts size (by simpa only [Nat.one_mul] using below)
      · by_cases divisible : size % factor = 0
        · have recovered : factor * (size / factor) = size :=
            Nat.mul_div_cancel_left' (Nat.dvd_of_mod_eq_zero divisible)
          have smaller : size / factor < lower := Nat.lt_of_mul_lt_mul_left (by
            rw [recovered]
            exact below)
          simpa only [scaleIndex, one, ↓reduceIte, divisible] using lowerCounts _ smaller
        · simp [scaleIndex, one, divisible]

/-- The source right fold preserves coefficients, order, and its choice minimum. -/
theorem choice_represents (items : List Key) (storage : Key → Stored)
    (indexes : Key → ValueIndex Value)
    (represented : ∀ key ∈ items, Represents (storage key) (indexes key)) :
    Represents (choice (items.map storage)) (choiceIndex (items.map indexes)) := by
  induction items with
  | nil => exact empty_represents
  | cons first rest ih =>
    have head := represented first (by simp)
    have tail := ih (fun key member => represented key (by simp [member]))
    constructor
    · exact Sparse.addSparse_ordered _ _ head.ordered tail.ordered
    · intro size
      change coefficient
        (Sparse.addSparse (storage first).series (choice (rest.map storage)).series) size =
          (indexes first).counts size + (choiceIndex (rest.map indexes)).counts size
      rw [Sparse.coefficient_addSparse, head.counts, tail.counts]
    · simpa only [choice, List.map_cons, choiceIndex, List.sum_cons] using
        choice_minimum_bound _ _ _ _ head.minimum tail.minimum

/-- The source paid constructor seed and ordered left fold use sparse products. -/
def folded (storage : Key → Stored) (children : List Key) : Stored :=
  children.foldl (fun built child => product built (storage child)) (pay constant)

private theorem fold_represents (children : List Key) (storage : Key → Stored)
    (indexes : Key → ValueIndex (Term Symbol))
    (represented : ∀ key, Represents (storage key) (indexes key))
    (before : Stored) (built : ValueIndex (List (Term Symbol) → Result))
    (initial : Represents before built) :
    Represents (children.foldl (fun accumulated child => product accumulated (storage child)) before)
      (children.foldl (fun accumulated child =>
        SourceSizedGroupedIndex.consumeChild accumulated (indexes child)) built) := by
  induction children generalizing before built with
  | nil => exact initial
  | cons first rest ih =>
    apply ih
    exact product_represents (fun function value => function value) before (storage first)
      (mapIndex SourceSizedGroupedIndex.prepend built) (indexes first)
      (map_represents SourceSizedGroupedIndex.prepend before built initial) (represented first)

/-- Every source prefix has the same counts as its independent typed fold. -/
theorem folded_represents (build : List (Term Symbol) → Result)
    (storage : Key → Stored) (indexes : Key → ValueIndex (Term Symbol))
    (represented : ∀ key, Represents (storage key) (indexes key)) (children : List Key) :
    Represents (folded storage children) (SourceSizedGroupedIndex.foldedIndex build indexes children) :=
  fold_represents children storage indexes represented (pay constant)
    (payIndex (constantIndex build)) (pay_represents constant _ (constant_represents build))

/-- Applying the final constructor function does not alter the sparse counts. -/
theorem built_represents (build : List (Term Symbol) → Result)
    (storage : Key → Stored) (indexes : Key → ValueIndex (Term Symbol))
    (represented : ∀ key, Represents (storage key) (indexes key)) (children : List Key) :
    Represents (folded storage children) (SourceSizedGroupedIndex.builtIndex build indexes children) := by
  unfold SourceSizedGroupedIndex.builtIndex
  exact map_represents (fun (function : List (Term Symbol) → Result) => function [])
    (folded storage children) (SourceSizedGroupedIndex.foldedIndex build indexes children)
    (folded_represents build storage indexes represented children)

/-- A group uses the literal representative read and positive group-length scale. -/
def group (storage : State → Stored) (children : List State) (positions : List Nat) : Stored :=
  match positions with
  | [] => empty
  | first :: _ =>
      match children[first]? with
      | none => empty
      | some state => scale positions.length (storage state)

/-- Representative failures and every nonempty group retain the actual count field. -/
theorem group_represents (storage : State → Stored) (indexes : State → ValueIndex (Term Symbol))
    (represented : ∀ state, Represents (storage state) (indexes state))
    (children : List State) (positions : List Nat) :
    Represents (group storage children positions) (SourceSizedGroupedIndex.groupIndex indexes children positions) := by
  cases positions with
  | nil => exact empty_represents
  | cons first rest =>
    cases selected : children[first]? with
    | none =>
      simpa only [group, SourceSizedGroupedIndex.groupIndex, selected] using
        (empty_represents (Value := Term Symbol))
    | some state =>
      simpa only [group, SourceSizedGroupedIndex.groupIndex, selected] using
        scale_represents (first :: rest).length (by simp) (storage state) (indexes state)
          (represented state)

/-- Preserve both literal row branches without constructing their value classes. -/
def rowStorage (storage : State → Stored) (row : Row State Symbol (List (List Nat))) : Stored :=
  if row.constraint = [] then folded storage row.children
  else folded (group storage row.children)
    (CompactGroups.childGroups row.children.length row.constraint)

/-- Ordinary and grouped source rows execute the represented sparse combinators. -/
theorem row_represents (storage : State → Stored) (indexes : State → ValueIndex (Term Symbol))
    (represented : ∀ state, Represents (storage state) (indexes state))
    (row : Row State Symbol (List (List Nat))) :
    Represents (rowStorage storage row) (SourceSizedGroupedIndex.rowIndex indexes row) := by
  by_cases plain : row.constraint = []
  · simpa only [rowStorage, SourceSizedGroupedIndex.rowIndex, plain, ite_true,
      SourceSizedGroupedIndex.plainIndex] using
      built_represents (Term.node row.label) storage indexes represented row.children
  · simpa only [rowStorage, SourceSizedGroupedIndex.rowIndex, plain, ite_false,
      SourceSizedGroupedIndex.groupedIndex] using
      built_represents
        (SourceSizedGroupedChainOrder.assemble row.label row.children.length
          (CompactGroups.childGroups row.children.length row.constraint))
        (group storage row.children) (SourceSizedGroupedIndex.groupIndex indexes row.children)
        (group_represents storage indexes represented row.children)
        (CompactGroups.childGroups row.children.length row.constraint)

/-- The source state chooses its stored rows with the sparse right fold. -/
def stateStorage (storage : State → Stored)
    (rows : List (Row State Symbol (List (List Nat)))) : Stored :=
  choice (rows.map (rowStorage storage))

/-- The full row list has exactly its independently built state count field. -/
theorem state_represents (storage : State → Stored) (indexes : State → ValueIndex (Term Symbol))
    (represented : ∀ state, Represents (storage state) (indexes state))
    (rows : List (Row State Symbol (List (List Nat)))) :
    Represents (stateStorage storage rows) (SourceSizedGroupedIndex.stateIndex indexes rows) :=
  choice_represents rows (rowStorage storage) (SourceSizedGroupedIndex.rowIndex indexes)
    (fun row _ => row_represents storage indexes represented row)

/-- Actual sparse lookup of the state fold reads its independent count field. -/
theorem state_lookup (storage : State → Stored) (indexes : State → ValueIndex (Term Symbol))
    (represented : ∀ state, Represents (storage state) (indexes state))
    (rows : List (Row State Symbol (List (List Nat)))) (size : Nat) :
    valueAtSize (stateStorage storage rows).series size =
      (SourceSizedGroupedIndex.stateIndex indexes rows).counts size :=
  (state_represents storage indexes represented rows).lookup size

/-- Execute finite sparse unfoldings with the same source minimum-presence gate. -/
def evaluate : Nat → (State → Bool) →
    (State → List (Row State Symbol (List (List Nat)))) → State → Stored
  | 0, _, _, _ => empty
  | fuel + 1, known, rows, state =>
      if known state then stateStorage (evaluate fuel known rows) (rows state) else empty

/-- Finite sparse unfoldings realize the independent source fields at every size. -/
theorem evaluate_represents (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (state : State) :
    Represents (evaluate fuel known rows state)
      (SourceSizedGroupedTableIndex.evaluate fuel known rows state) := by
  induction fuel generalizing state with
  | zero => exact empty_represents
  | succ fuel ih =>
    cases present : known state with
    | false =>
      simpa only [evaluate, SourceSizedGroupedTableIndex.evaluate, present,
        Bool.false_eq_true, ite_false] using (empty_represents (Value := Term Symbol))
    | true =>
      simpa only [evaluate, SourceSizedGroupedTableIndex.evaluate, present, ite_true] using
        state_represents (evaluate fuel known rows)
          (SourceSizedGroupedTableIndex.evaluate fuel known rows) ih (rows state)

/-- The finite source storage reads the same count as its independent unfolding. -/
theorem evaluate_lookup (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (state : State) (size : Nat) :
    valueAtSize (evaluate fuel known rows state).series size =
      (SourceSizedGroupedTableIndex.evaluate fuel known rows state).counts size :=
  (evaluate_represents fuel known rows state).lookup size

/-- The request-computed finite bound suffices for the represented count read. -/
theorem requested_count (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (size : Nat) (state : State) :
    valueAtSize (evaluate (size + 1) known rows state).series size =
      SourceSizedGroupedTableIndex.countAt known rows size state :=
  evaluate_lookup (size + 1) known rows state size

/-- The finite storage count agrees with the existing independent grouped classes. -/
theorem requested_classes (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : SourceSizedGroupedTableIndex.MissingEmpty known rows) (size : Nat) (state : State) :
    valueAtSize (evaluate (size + 1) known rows state).series size =
      (SourceSizedGroupedClasses.classes rows size state).length := by
  rw [requested_count, SourceSizedGroupedTableIndex.countAt_eq known rows missing]

end MicroCFTA.SourceSizedGroupedSparseFields
