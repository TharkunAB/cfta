import MicroCFTA.RecursiveSize
import MicroCFTA.Sparse

/-!
# Size-class positions and replay ranks

`sizeClassOf` and `sizeMajorRank` use the finite ordered count tables from
`Ranked.Internal.Size`. Zero-count classes are allowed. Positions identify
runs. Distinct positions can decode to equal terms in ambiguous automata.

The tables and arithmetic use finite lists and natural numbers. Lazy infinite
class tables, machine integer conversions, and the concrete map storage used
by `Table.tablePosition` require separate correspondence proofs. `planPosition`
covers source, map, choice, and application nodes. Shared and sized Haskell
plan constructors are not encoded here. `termPosition` is a reference search;
its equivalence to the cached bottom-up worker is not asserted.
-/

namespace MicroCFTA.SizedRank

open Language RecursiveSize

/-- A size and a rank within that size class. -/
structure Position where
  size : Nat
  rank : Nat
  deriving DecidableEq, Repr

/-- Find a size class by subtracting the preceding class counts. -/
def sizeClassOf : Sparse.Series Nat → Nat → Option Position
  | [], _ => none
  | (size, count) :: rest, rank =>
      if rank < count then some ⟨size, rank⟩ else sizeClassOf rest (rank - count)

/-- Add the counts before the first class whose size is not smaller. -/
def countBelow : Sparse.Series Nat → Nat → Nat
  | [], _ => 0
  | (size, count) :: rest, wanted =>
      if size < wanted then count + countBelow rest wanted else 0

/-- Place a class position after every smaller class. -/
def sizeMajorRank (counts : Sparse.Series Nat) (position : Position) : Nat :=
  countBelow counts position.size + position.rank

/-- A valid position belongs to a listed size class and lies below its count. -/
def Valid (counts : Sparse.Series Nat) (position : Position) : Prop :=
  ∃ count, (position.size, count) ∈ counts ∧ position.rank < count

/-- Every returned position lies inside a listed class. -/
theorem sizeClassOf_valid (counts : Sparse.Series Nat) (rank : Nat) (position : Position)
    (found : sizeClassOf counts rank = some position) : Valid counts position := by
  induction counts generalizing rank with
  | nil => cases found
  | cons entry counts ih =>
      rcases entry with ⟨size, count⟩
      simp only [sizeClassOf] at found
      split at found
      next inside =>
        have same := Option.some.inj found
        subst position
        exact ⟨count, by simp, inside⟩
      next outside =>
        obtain ⟨n, member, inside⟩ := ih _ found
        exact ⟨n, by simp [member], inside⟩

/-- Subtracting a complete leading class preserves the remaining position. -/
theorem sizeClassOf_offset (size count rank : Nat) (rest : Sparse.Series Nat) :
    sizeClassOf ((size, count) :: rest) (count + rank) = sizeClassOf rest rank := by
  simp [sizeClassOf, show ¬count + rank < count by omega]

/-- Converting a valid class position to a global rank and back preserves it. -/
theorem sizeClassOf_sizeMajorRank (counts : Sparse.Series Nat) (ordered : Sparse.Ordered counts)
    (position : Position) (valid : Valid counts position) :
    sizeClassOf counts (sizeMajorRank counts position) = some position := by
  induction counts with
  | nil => obtain ⟨_, impossible, _⟩ := valid; simp at impossible
  | cons entry counts ih =>
      rcases entry with ⟨size, count⟩
      obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
      obtain ⟨n, member, inside⟩ := valid
      rcases List.mem_cons.mp member with same | member
      · have hs : position.size = size := congrArg Prod.fst same
        have hn : n = count := congrArg Prod.snd same
        subst n
        cases position with
        | mk actual rank =>
            dsimp only at hs
            subst actual
            simp [sizeMajorRank, countBelow, sizeClassOf, inside]
      · have before : size < position.size := headBefore _ member
        have tail := ih tailOrdered ⟨n, member, inside⟩
        simpa only [sizeMajorRank, countBelow, ite_eq_left before, Nat.add_assoc,
          sizeClassOf_offset] using tail

/-- Converting a global rank to its class position and back preserves the rank. -/
theorem sizeMajorRank_sizeClassOf (counts : Sparse.Series Nat) (ordered : Sparse.Ordered counts)
    (rank : Nat) (position : Position) (found : sizeClassOf counts rank = some position) :
    sizeMajorRank counts position = rank := by
  induction counts generalizing rank with
  | nil => cases found
  | cons entry counts ih =>
      rcases entry with ⟨size, count⟩
      obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
      simp only [sizeClassOf] at found
      split at found
      next inside =>
        have same := Option.some.inj found
        subst position
        simp [sizeMajorRank, countBelow]
      next outside =>
        obtain ⟨n, member, _⟩ := sizeClassOf_valid counts _ position found
        have before : size < position.size := headBefore _ member
        have tail := ih tailOrdered _ found
        simp only [sizeMajorRank, countBelow, ite_eq_left before]
        unfold sizeMajorRank at tail
        omega

/-- The class search succeeds exactly below the total number of ranks. -/
theorem sizeClassOf_exists_iff (counts : Sparse.Series Nat) (rank : Nat) :
    (∃ position, sizeClassOf counts rank = some position) ↔ rank < (counts.map Prod.snd).sum := by
  induction counts generalizing rank with
  | nil => simp [sizeClassOf]
  | cons entry counts ih =>
      rcases entry with ⟨size, count⟩
      simp only [List.map_cons, List.sum_cons, sizeClassOf]
      by_cases inside : rank < count
      · simp [inside]; omega
      · rw [ite_eq_right inside, ih]
        omega

/-- The prefix counter is the sum over `takeWhile`, as in the Haskell worker. -/
theorem countBelow_takeWhile (counts : Sparse.Series Nat) (size : Nat) :
    countBelow counts size =
      ((counts.takeWhile (fun entry => decide (entry.1 < size))).map Prod.snd).sum := by
  induction counts with
  | nil => rfl
  | cons entry counts ih =>
      rcases entry with ⟨actual, count⟩
      by_cases smaller : actual < size <;> simp [countBelow, smaller, ih]

/-- A class offset cannot exceed the total number of ranks. -/
theorem sizeMajorRank_bound (counts : Sparse.Series Nat) (ordered : Sparse.Ordered counts)
    (position : Position) (valid : Valid counts position) :
    sizeMajorRank counts position < (counts.map Prod.snd).sum :=
  (sizeClassOf_exists_iff counts _).mp
    ⟨position, sizeClassOf_sizeMajorRank counts ordered position valid⟩

/-- Place a branch rank after the same-size counts of all earlier branches. -/
def choicePosition (counts : List Nat) (branch rank : Nat) : Nat :=
  (counts.take branch).sum + rank

/-- Find an ordered branch and remove the counts of all earlier branches. -/
def choiceSplit : List Nat → Nat → Option (Nat × Nat)
  | [], _ => none
  | count :: counts, rank =>
      if rank < count then some (0, rank)
      else (choiceSplit counts (rank - count)).map (fun position => (position.1 + 1, position.2))

/-- Choice selection recovers the original branch and its valid local rank. -/
theorem choiceSplit_choicePosition (counts : List Nat) (branch rank count : Nat)
    (present : counts[branch]? = some count) (valid : rank < count) :
    choiceSplit counts (choicePosition counts branch rank) = some (branch, rank) := by
  induction counts generalizing branch with
  | nil => simp at present
  | cons head counts ih =>
      cases branch with
      | zero =>
          have same : head = count := by simpa using present
          subst head
          simp [choicePosition, choiceSplit, valid]
      | succ branch =>
          have tail : counts[branch]? = some count := by simpa using present
          have found := ih branch tail
          simp only [choicePosition, List.take_succ_cons, List.sum_cons] at ⊢ found
          simp only [choiceSplit, show ¬head + (counts.take branch).sum + rank < head by omega,
            ite_false, show head + (counts.take branch).sum + rank - head =
              (counts.take branch).sum + rank by omega, found, Option.map_some]

/-- Place a member at the sum of the lengths of all preceding groups. -/
theorem get_choicePosition (groups : List (List α)) (branch rank : Nat)
    (branchValid : branch < groups.length) (rankValid : rank < (groups[branch]).length) :
    groups.flatten[choicePosition (groups.map List.length) branch rank]? = (groups[branch])[rank]? := by
  induction groups generalizing branch with
  | nil => simp at branchValid
  | cons group groups ih =>
      cases branch with
      | zero =>
          simp only [List.getElem_cons_zero] at rankValid ⊢
          simp only [choicePosition, List.take_zero, List.sum_nil, Nat.zero_add, List.flatten_cons]
          exact List.getElem?_append_left rankValid
      | succ branch =>
          have branchValid' : branch < groups.length := by simpa using branchValid
          have rankValid' : rank < (groups[branch]).length := by simpa using rankValid
          have found := ih branch branchValid' rankValid'
          simp only [choicePosition, List.map_cons, List.take_succ_cons, List.sum_cons,
            List.flatten_cons, List.getElem_cons_succ]
          rw [List.getElem?_append_right (by omega)]
          simpa only [choicePosition, Nat.add_assoc, Nat.add_sub_cancel_left] using found

/-- A product position uses ascending left sizes and left-major ranks within a split. -/
def productPosition (left right : Nat → Nat) (first second : Position) : Position :=
  let size := first.size + second.size
  ⟨size, ((List.range first.size).map (fun split => left split * right (size - split))).sum +
    Probability.pairRank (right second.size) first.rank second.rank⟩

/-- Product sizes are the sum of the two component sizes. -/
theorem productPosition_size (left right : Nat → Nat) (first second : Position) :
    (productPosition left right first second).size = first.size + second.size := rfl

/-- Addition can be distributed through a finite sum. -/
theorem sum_map_add (items : List α) (left right : α → Nat) :
    (items.map (fun item => left item + right item)).sum =
      (items.map left).sum + (items.map right).sum := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

/-- A range contains each size once. Only its matching weighted entry contributes. -/
theorem sum_point (bound size value : Nat) (weight : Nat → Nat) :
    ((List.range bound).map (fun n => if size = n then value * weight n else 0)).sum =
      if size < bound then value * weight size else 0 := by
  induction bound with
  | zero => simp
  | succ bound ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      by_cases earlier : size < bound
      · have different : size ≠ bound := by omega
        simp [earlier, different, show size < bound + 1 by omega]
      · by_cases same : size = bound
        · subst size; simp
        · simp [earlier, same, show ¬size < bound + 1 by omega]

/-- Summing sparse coefficients over a finite range equals summing their stored entries. -/
theorem weighted_coefficient_sum (series : Sparse.Series Nat) (bound : Nat) (weight : Nat → Nat) :
    ((List.range bound).map (fun size => Sparse.coefficient series size * weight size)).sum =
      ((series.filter (fun entry => decide (entry.1 < bound))).map
        (fun entry => entry.2 * weight entry.1)).sum := by
  induction series with
  | nil => simp [Sparse.coefficient, sum_constant]
  | cons entry series ih =>
      rcases entry with ⟨size, value⟩
      have expand (actual : Nat) :
          Sparse.coefficient ((size, value) :: series) actual * weight actual =
            (if size = actual then value * weight actual else 0) +
              Sparse.coefficient series actual * weight actual := by
        simp only [Sparse.coefficient, Nat.add_mul]
        split <;> simp_all
      simp only [expand]
      rw [sum_map_add, sum_point, ih]
      by_cases within : size < bound <;> simp [within]

/-- In an ordered sparse table, filtering smaller sizes is the initial smaller-size prefix. -/
theorem filter_lt_eq_takeWhile (series : Sparse.Series Nat) (ordered : Sparse.Ordered series)
    (bound : Nat) : series.filter (fun entry => decide (entry.1 < bound)) =
      series.takeWhile (fun entry => decide (entry.1 < bound)) := by
  induction series with
  | nil => rfl
  | cons entry series ih =>
      obtain ⟨before, tailOrdered⟩ := List.pairwise_cons.mp ordered
      by_cases smaller : entry.1 < bound
      · simp [smaller, ih tailOrdered]
      · have none : series.filter (fun other => decide (other.1 < bound)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro other member
          have next := before other member
          simpa only [decide_eq_true_eq] using (show ¬other.1 < bound by omega)
        simp [smaller, none]

/-- The sparse `productPosition` formula sums only stored classes before the chosen left size. -/
def sparseProductPosition (left right : Sparse.Series Nat) (first second : Position) : Position :=
  let size := first.size + second.size
  ⟨size, ((left.takeWhile (fun entry => decide (entry.1 < first.size))).map
      (fun entry => entry.2 * Sparse.valueAtSize right (size - entry.1))).sum +
    first.rank * Sparse.valueAtSize right second.size + second.rank⟩

/-- Dense product offsets equal the Haskell sparse prefix formula. -/
theorem sparseProductPosition_correct (left right : Sparse.Series Nat) (ordered : Sparse.Ordered left)
    (first second : Position) :
    sparseProductPosition left right first second =
      productPosition (Sparse.valueAtSize left) (Sparse.valueAtSize right) first second := by
  unfold sparseProductPosition productPosition Probability.pairRank
  simp only [Sparse.valueAtSize_correct left ordered]
  rw [weighted_coefficient_sum, filter_lt_eq_takeWhile left ordered]
  congr 1
  omega

/-- The finite table of split counts includes all sizes from zero to the total. -/
def splitCounts (left right : Nat → Nat) (size : Nat) : Sparse.Series Nat :=
  (List.range (size + 1)).map (fun split => (split, left split * right (size - split)))

/-- Decode a product class position by its split and its mixed-radix rank. -/
def productSplit (left right : Nat → Nat) (position : Position) : Option (Position × Position) := do
  let split ← sizeClassOf (splitCounts left right position.size) position.rank
  let ranks := Probability.splitRank (right (position.size - split.size)) split.rank
  pure (⟨split.size, ranks.1⟩, ⟨position.size - split.size, ranks.2⟩)

/-- Finite split tables have strictly increasing left sizes. -/
theorem splitCounts_ordered (left right : Nat → Nat) (size : Nat) :
    Sparse.Ordered (splitCounts left right size) := by
  apply List.pairwise_map.mpr
  exact range_ordered (size + 1)

/-- Taking the sizes below a bound from a finite range returns its initial range. -/
theorem takeWhile_range (bound size : Nat) (within : size ≤ bound) :
    (List.range bound).takeWhile (fun n => decide (n < size)) = List.range size := by
  induction bound generalizing size with
  | zero =>
      have same : size = 0 := by omega
      subst size
      rfl
  | succ bound ih =>
      cases size with
      | zero => simp [List.range_succ_eq_map]
      | succ size =>
          have within' : size ≤ bound := by omega
          simp only [List.range_succ_eq_map, List.takeWhile_cons, Nat.zero_lt_succ,
            decide_true, ite_true, List.takeWhile_map, Function.comp_def, Nat.succ_lt_succ_iff]
          rw [ih size within']

/-- A dense class table has the sum of all earlier coefficients as its offset. -/
theorem countBelow_range (counts : Nat → Nat) (bound size : Nat) (within : size ≤ bound) :
    countBelow ((List.range bound).map (fun n => (n, counts n))) size =
      ((List.range size).map counts).sum := by
  rw [countBelow_takeWhile]
  have before : ((List.range bound).map (fun n => (n, counts n))).takeWhile
      (fun entry => decide (entry.1 < size)) = (List.range size).map (fun n => (n, counts n)) := by
    rw [List.takeWhile_map]
    congr 1
    exact takeWhile_range bound size within
  rw [before]
  simp only [List.map_map, Function.comp_def]

/-- The product encoder recovers both component positions after split decoding. -/
theorem productSplit_productPosition (left right : Nat → Nat) (first second : Position)
    (firstValid : first.rank < left first.size) (secondValid : second.rank < right second.size) :
    productSplit left right (productPosition left right first second) = some (first, second) := by
  let total := first.size + second.size
  let within := Probability.pairRank (right second.size) first.rank second.rank
  have subtraction : total - first.size = second.size := by simp [total]
  have valid : Valid (splitCounts left right total) ⟨first.size, within⟩ := by
    refine ⟨left first.size * right second.size, ?_, Probability.pairRank_lt firstValid secondValid⟩
    apply List.mem_map.mpr
    exact ⟨first.size, List.mem_range.mpr (by dsimp [total]; omega), by simp [subtraction]⟩
  have selected := sizeClassOf_sizeMajorRank (splitCounts left right total)
    (splitCounts_ordered left right total) ⟨first.size, within⟩ valid
  have offset : countBelow (splitCounts left right total) first.size =
      ((List.range first.size).map (fun split => left split * right (total - split))).sum :=
    countBelow_range _ (total + 1) first.size (by dsimp [total]; omega)
  unfold sizeMajorRank at selected
  rw [offset] at selected
  simp only [productSplit, productPosition]
  change (sizeClassOf (splitCounts left right total) (_ + within)).bind _ = _
  rw [selected]
  simp only [Option.bind_some, Nat.add_sub_cancel_left, within, Probability.split_pair secondValid]
  rfl

/-- Recombining a selected product split preserves the original class rank. -/
theorem productPosition_selectedSplit (left right : Nat → Nat) (position split : Position)
    (selected : sizeClassOf (splitCounts left right position.size) position.rank = some split) :
    productPosition left right
      ⟨split.size, split.rank / right (position.size - split.size)⟩
      ⟨position.size - split.size, split.rank % right (position.size - split.size)⟩ = position := by
  obtain ⟨count, member, _⟩ := sizeClassOf_valid _ _ _ selected
  obtain ⟨size, inRange, same⟩ := List.mem_map.mp member
  have sizeSame : size = split.size := congrArg Prod.fst same
  have within : split.size ≤ position.size := by
    have bound := List.mem_range.mp inRange
    omega
  have totalSame : split.size + (position.size - split.size) = position.size := by omega
  have replay := sizeMajorRank_sizeClassOf (splitCounts left right position.size)
    (splitCounts_ordered left right position.size) position.rank split selected
  have offset := countBelow_range (fun size => left size * right (position.size - size))
    (position.size + 1) split.size (by omega)
  change countBelow (splitCounts left right position.size) split.size = _ at offset
  unfold sizeMajorRank at replay
  rw [offset] at replay
  unfold productPosition
  simp only [totalSame]
  have join : Probability.pairRank (right (position.size - split.size))
      (split.rank / right (position.size - split.size))
      (split.rank % right (position.size - split.size)) = split.rank :=
    Probability.pair_split _ _
  rw [join, replay]

/-- Product position and split decoding are inverses on all returned positions. -/
theorem productPosition_productSplit (left right : Nat → Nat) (position : Position)
    (first second : Position) (found : productSplit left right position = some (first, second)) :
    productPosition left right first second = position := by
  cases selected : sizeClassOf (splitCounts left right position.size) position.rank with
  | none => simp [productSplit, selected] at found
  | some split =>
      have same :
          (⟨split.size, split.rank / right (position.size - split.size)⟩,
            ⟨position.size - split.size, split.rank % right (position.size - split.size)⟩) =
              (first, second) := by
        simpa [productSplit, selected, Probability.splitRank] using found
      obtain ⟨firstSame, secondSame⟩ := Prod.mk.inj same
      rw [← firstSame, ← secondSame]
      exact productPosition_selectedSplit left right position split selected

/-- Product positions replay the same pair in the class list. -/
theorem productPosition_replay (functions : Nat → List (α → β)) (arguments : Nat → List α)
    (first second : Position) (firstValid : first.rank < (functions first.size).length)
    (secondValid : second.rank < (arguments second.size).length) :
    ((List.range (first.size + second.size + 1)).flatMap fun split =>
      Decoder.applyValues (functions split) (arguments (first.size + second.size - split)))[(productPosition (fun size => (functions size).length)
        (fun size => (arguments size).length) first second).rank]? =
      (functions first.size)[first.rank]?.bind (fun f => (arguments second.size)[second.rank]?.map f) := by
  let total := first.size + second.size
  let pair := Probability.pairRank (arguments second.size).length first.rank second.rank
  have valid : pair < (Decoder.applyValues (functions first.size) (arguments (total - first.size))).length := by
    rw [Decoder.length_applyValues]
    simpa only [total, Nat.add_sub_cancel_left] using Probability.pairRank_lt firstValid secondValid
  have replay := get_class_offset
    (fun split => Decoder.applyValues (functions split) (arguments (total - split)))
    total first.size pair (by dsimp [total]; omega) valid
  simp only [Decoder.length_applyValues] at replay
  change _ = _ at replay
  unfold productPosition
  rw [replay]
  rw [Decoder.get_applyValues]
  have bounded := Probability.pairRank_lt firstValid secondValid
  dsimp only [pair]
  simp only [total, Nat.add_sub_cancel_left, ite_eq_left bounded]
  have split := Probability.split_pair secondValid (left := first.rank)
  simpa only [Probability.splitRank, Probability.pairRank] using
    congrArg (fun p : Nat × Nat => (functions first.size)[p.1]?.bind
      (fun f => (arguments second.size)[p.2]?.map f)) split

/-- List ordinary replay ranks in each size class of a finite decoder plan. -/
def planClassRanks : Decoder.Plan α → Nat → List Nat
  | .source values, size => if size = 1 then List.range values.length else []
  | .map _ input, size => planClassRanks input size
  | .choice left right, size =>
      planClassRanks left size ++ (planClassRanks right size).map (Decoder.count left + ·)
  | .ap functions arguments, size =>
      (List.range (size + 1)).flatMap fun split =>
        Decoder.applyValues ((planClassRanks functions split).map
          (fun function argument => Probability.pairRank (Decoder.count arguments) function argument))
          (planClassRanks arguments (size - split))

/-- Convert a finite plan's ordinary rank to its compositional size-class position. -/
def planPosition : (plan : Decoder.Plan α) → Nat → Option Position
  | .source values, rank => if rank < values.length then some ⟨1, rank⟩ else none
  | .map _ input, rank => planPosition input rank
  | .choice left right, rank =>
      if rank < Decoder.count left then planPosition left rank
      else (planPosition right (rank - Decoder.count left)).map fun position =>
        ⟨position.size, (planClassRanks left position.size).length + position.rank⟩
  | .ap functions arguments, rank =>
      if rank < Decoder.count functions * Decoder.count arguments then do
        let first ← planPosition functions (rank / Decoder.count arguments)
        let second ← planPosition arguments (rank % Decoder.count arguments)
        pure (productPosition (fun size => (planClassRanks functions size).length)
          (fun size => (planClassRanks arguments size).length) first second)
      else none

/-- Every valid ordinary plan rank has a compositional class position. -/
theorem planPosition_complete (plan : Decoder.Plan α) (rank : Nat) (valid : rank < Decoder.count plan) :
    ∃ position, planPosition plan rank = some position := by
  induction plan generalizing rank with
  | source values => exact ⟨⟨1, rank⟩, by simp [planPosition, show rank < values.length from valid]⟩
  | map transform input ih => exact ih rank valid
  | choice left right ihl ihr =>
      by_cases inLeft : rank < Decoder.count left
      · obtain ⟨position, found⟩ := ihl rank inLeft
        exact ⟨position, by simp [planPosition, inLeft, found]⟩
      · have inRight : rank - Decoder.count left < Decoder.count right := by
          change rank < Decoder.count left + Decoder.count right at valid
          omega
        obtain ⟨position, found⟩ := ihr _ inRight
        exact ⟨⟨position.size, (planClassRanks left position.size).length + position.rank⟩,
          by simp [planPosition, inLeft, found]⟩
  | ap functions arguments ihf ihx =>
      obtain ⟨leftValid, rightValid⟩ := Probability.split_lt valid
      obtain ⟨first, foundFirst⟩ := ihf _ leftValid
      obtain ⟨second, foundSecond⟩ := ihx _ rightValid
      dsimp only [Probability.splitRank] at foundFirst foundSecond
      refine ⟨productPosition (fun size => (planClassRanks functions size).length)
        (fun size => (planClassRanks arguments size).length) first second, ?_⟩
      simp [planPosition, show rank < Decoder.count functions * Decoder.count arguments from valid,
        foundFirst, foundSecond]

/-- Invalid ordinary plan ranks have no class position. -/
theorem planPosition_none (plan : Decoder.Plan α) (rank : Nat) (invalid : Decoder.count plan ≤ rank) :
    planPosition plan rank = none := by
  induction plan generalizing rank with
  | source values => simp [planPosition, show ¬rank < values.length by exact Nat.not_lt.mpr invalid]
  | map transform input ih => exact ih rank invalid
  | choice left right ihl ihr =>
      change Decoder.count left + Decoder.count right ≤ rank at invalid
      have inRight : Decoder.count right ≤ rank - Decoder.count left := by omega
      simp [planPosition, show ¬rank < Decoder.count left by omega, ihr _ inRight]
  | ap functions arguments ihf ihx =>
      simp [planPosition, show ¬rank < Decoder.count functions * Decoder.count arguments from Nat.not_lt.mpr invalid]

/-- Selecting the computed class position recovers the original ordinary plan rank. -/
theorem planPosition_replay (plan : Decoder.Plan α) (rank : Nat) (position : Position)
    (found : planPosition plan rank = some position) :
    (planClassRanks plan position.size)[position.rank]? = some rank := by
  induction plan generalizing rank position with
  | source values =>
      simp only [planPosition] at found
      split at found
      next valid =>
        have same := Option.some.inj found
        subst position
        simp [planClassRanks, valid]
      next invalid => cases found
  | map transform input ih => exact ih rank position found
  | choice left right ihl ihr =>
      simp only [planPosition] at found
      split at found
      next inLeft =>
        have replay := ihl rank position found
        have valid := (List.getElem?_eq_some_iff.mp replay).1
        rw [planClassRanks, List.getElem?_append_left valid]
        exact replay
      next inRight =>
        cases rightFound : planPosition right (rank - Decoder.count left) with
        | none => simp [rightFound] at found
        | some part =>
            have same : (⟨part.size, (planClassRanks left part.size).length + part.rank⟩ : Position) =
                position := by simpa [rightFound] using found
            subst position
            have replay := ihr _ part rightFound
            simp only [planClassRanks]
            rw [List.getElem?_append_right (by omega)]
            simp only [Nat.add_sub_cancel_left, List.getElem?_map, replay, Option.map_some]
            congr 1
            omega
  | ap functions arguments ihf ihx =>
      simp only [planPosition] at found
      split at found
      next valid =>
        cases firstFound : planPosition functions (rank / Decoder.count arguments) with
        | none => simp [firstFound] at found
        | some first =>
            cases secondFound : planPosition arguments (rank % Decoder.count arguments) with
            | none => simp [firstFound, secondFound] at found
            | some second =>
                have same : productPosition (fun size => (planClassRanks functions size).length)
                    (fun size => (planClassRanks arguments size).length) first second = position := by
                  simpa [firstFound, secondFound] using found
                subst position
                have firstReplay := ihf _ first firstFound
                have secondReplay := ihx _ second secondFound
                have firstValid := (List.getElem?_eq_some_iff.mp firstReplay).1
                have secondValid := (List.getElem?_eq_some_iff.mp secondReplay).1
                have replay := productPosition_replay
                  (fun size => (planClassRanks functions size).map
                    (fun function argument => Probability.pairRank (Decoder.count arguments) function argument))
                  (planClassRanks arguments) first second (by simpa using firstValid) secondValid
                simp only [List.length_map] at replay
                change _ = _ at replay
                rw [planClassRanks, productPosition_size]
                rw [replay]
                simp only [List.getElem?_map, firstReplay, secondReplay, Option.map_some, Option.bind_some]
                exact congrArg some (Probability.pair_split (Decoder.count arguments) rank)
      next invalid => cases found

/-- Finite plan positions exist exactly for valid ordinary ranks. -/
theorem planPosition_exists_iff (plan : Decoder.Plan α) (rank : Nat) :
    (∃ position, planPosition plan rank = some position) ↔ rank < Decoder.count plan := by
  constructor
  · rintro ⟨position, found⟩
    by_cases valid : rank < Decoder.count plan
    · exact valid
    · rw [planPosition_none plan rank (by omega)] at found
      cases found
  · exact planPosition_complete plan rank

/-- Find the first rank of a value in a finite ordered run list. -/
def rankOf [DecidableEq α] (values : List α) (value : α) : Option Nat :=
  let rank := values.idxOf value
  if rank < values.length then some rank else none

/-- A returned rank replays the requested value. Duplicate values are allowed. -/
theorem rankOf_replay [DecidableEq α] (values : List α) (value : α) (rank : Nat)
    (found : rankOf values value = some rank) : values[rank]? = some value := by
  unfold rankOf at found
  dsimp only at found
  split at found
  next inside =>
    have same := Option.some.inj found
    rw [← same, List.getElem?_eq_getElem inside, List.getElem_idxOf inside]
  next outside => cases found

/-- A value has a reference rank exactly when it occurs in the run list. -/
theorem rankOf_exists_iff [DecidableEq α] (values : List α) (value : α) :
    (∃ rank, rankOf values value = some rank) ↔ value ∈ values := by
  constructor
  · rintro ⟨rank, found⟩
    exact List.mem_of_getElem? (rankOf_replay values value rank found)
  · intro member
    refine ⟨values.idxOf value, ?_⟩
    simp [rankOf, List.idxOf_lt_length_of_mem member]

/-- Ranking a decoded value recovers its rank when every value has only one run. -/
theorem rankOf_get [DecidableEq α] (values : List α) (unambiguous : values.Nodup)
    (rank : Nat) (valid : rank < values.length) : rankOf values values[rank] = some rank := by
  simp [rankOf, unambiguous.idxOf_getElem rank valid, valid]

/-- The existing structural equality procedure gives a decidable term comparison. -/
local instance termDecidableEq [DecidableEq Symbol] : DecidableEq (Term Symbol) :=
  fun left right => decidable_of_iff (termEq left right = true) (termEq_correct left right)

/-- Find a term's first rank in its exact node-count class.
This finite reference search does not model the bottom-up worker's map cache. -/
def termPosition [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (term : Term Symbol) : Option Position :=
  (rankOf (RecursiveSize.enumerate automaton (nodeSize term) state) term).map (fun rank => ⟨nodeSize term, rank⟩)

/-- Decode a size-class position through the verified compiled plan. -/
def replayPosition (automaton : Automaton State Symbol) (state : State)
    (position : Position) : Option (Term Symbol) :=
  Decoder.decode (Decoder.normalize (compileAt automaton position.size state)) position.rank

/-- The reference rank of a term always decodes to that term. -/
theorem termPosition_replay [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (term : Term Symbol) (position : Position)
    (found : termPosition automaton state term = some position) :
    replayPosition automaton state position = some term := by
  cases ranked : rankOf (RecursiveSize.enumerate automaton (nodeSize term) state) term with
  | none => simp [termPosition, ranked] at found
  | some rank =>
      have same : (⟨nodeSize term, rank⟩ : Position) = position := by
        simpa [termPosition, ranked] using found
      subst position
      rw [replayPosition, decode_compileAt]
      exact rankOf_replay _ _ rank ranked

/-- The reference rank search succeeds exactly on the accepted language. -/
theorem termPosition_exists_iff [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (state : State) (term : Term Symbol) :
    (∃ position, termPosition automaton state term = some position) ↔ Accepts automaton state term := by
  constructor
  · rintro ⟨position, found⟩
    have replay := termPosition_replay automaton state term position found
    rw [replayPosition, decode_compileAt] at replay
    exact ((RecursiveSize.mem_enumerate_iff automaton plain position.size state term).mp
      (List.mem_of_getElem? replay)).1
  · intro accepted
    have member := (RecursiveSize.mem_enumerate_iff automaton plain (nodeSize term) state term).mpr ⟨accepted, rfl⟩
    obtain ⟨rank, ranked⟩ := (rankOf_exists_iff _ _).mpr member
    exact ⟨⟨nodeSize term, rank⟩, by simp [termPosition, ranked]⟩

/-- Every reference position records the actual node count and a valid class rank. -/
theorem termPosition_valid [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (term : Term Symbol) (position : Position)
    (found : termPosition automaton state term = some position) :
    position.size = nodeSize term ∧ position.rank < countAt automaton position.size state := by
  cases ranked : rankOf (RecursiveSize.enumerate automaton (nodeSize term) state) term with
  | none => simp [termPosition, ranked] at found
  | some rank =>
      have same : (⟨nodeSize term, rank⟩ : Position) = position := by
        simpa [termPosition, ranked] using found
      subst position
      refine ⟨rfl, ?_⟩
      rw [countAt_correct]
      exact (List.getElem?_eq_some_iff.mp (rankOf_replay _ _ rank ranked)).1

/-- Term-to-rank conversion also replays at the global size-major offset. -/
theorem termPosition_sizeMajor_replay [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (term : Term Symbol) (position : Position) (bound : Nat)
    (found : termPosition automaton state term = some position) (within : position.size ≤ bound) :
    Decoder.decode (Decoder.normalize (compileAtMost automaton bound state))
      (classOffset automaton position.size state + position.rank) = some term := by
  rw [sizeMajor_rank_replay automaton bound position.size state position.rank within
    (termPosition_valid automaton state term position found).2]
  exact termPosition_replay automaton state term position found

/-- Run uniqueness in each exact size class is the required unambiguity condition. -/
def Unambiguous (automaton : Automaton State Symbol) : Prop :=
  ∀ state size, (RecursiveSize.enumerate automaton size state).Nodup

/-- With unambiguity, decoding then ranking recovers the original class position. -/
theorem termPosition_of_replay [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (unambiguous : Unambiguous automaton)
    (state : State) (position : Position) (term : Term Symbol)
    (replayed : replayPosition automaton state position = some term) :
    termPosition automaton state term = some position := by
  rw [replayPosition, decode_compileAt] at replayed
  obtain ⟨valid, same⟩ := List.getElem?_eq_some_iff.mp replayed
  have sized := (RecursiveSize.mem_enumerate_iff automaton plain position.size state term).mp
    (List.mem_of_getElem? replayed)
  rw [termPosition, sized.2]
  have ranked := rankOf_get (RecursiveSize.enumerate automaton position.size state)
    (unambiguous state position.size) position.rank valid
  rw [same] at ranked
  rw [ranked]
  cases position
  rfl

/-- Equal decoded values do not imply equal run ranks without unambiguity. -/
theorem duplicate_rank_counterexample :
    ([7, 7] : List Nat)[0]? = some 7 ∧ ([7, 7] : List Nat)[1]? = some 7 ∧
      rankOf ([7, 7] : List Nat) 7 = some 0 ∧ rankOf ([7, 7] : List Nat) 7 ≠ some 1 := by
  decide

end MicroCFTA.SizedRank


