import MicroCFTA.RecursiveFieldBounds
import MicroCFTA.SupportJoin

/-!
# Source recursive join accumulation

The operation precedes every argument. The source accumulates their terms
from left to right and uses each prefix's value counts for the next product.
The selector uses productSplit. It does not enumerate earlier members.
-/
namespace MicroCFTA.RecursiveJoinFields
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct

/-- The count and selector fields of a typed source size index. -/
structure ValueIndex (Value : Type) where
  counts : Nat → Nat
  select : Position → Option Value

/-- Each size index selects exactly its finite class interval. -/
def Indexed (index : ValueIndex Value) : Prop :=
  ∀ position, (∃ value, index.select position = some value) ↔ position.rank < index.counts position.size

/-- The operation and its accumulated argument forest. -/
abbrev Accumulated (Symbol : Type) := EngineTerm Symbol × List (EngineTerm Symbol)

/-- Read the independent term field through the source's value-count interval. -/
def termIndex (field : Finite Symbol) : ValueIndex (EngineTerm Symbol) := ⟨field.counts, field.select⟩

/-- The initial mapIndex (,[]) retains the operation term and no argument. -/
def start (operation : Finite Symbol) : ValueIndex (Accumulated Symbol) :=
  ⟨operation.counts, fun position => (operation.select position).map (fun term => (term, []))⟩

/-- Source product counts include every nonnegative size split. -/
def convolve (left right : Nat → Nat) (size : Nat) : Nat :=
  ((List.range (size + 1)).map fun split => left split * right (size - split)).sum

/-- Append one independently selected argument to the accumulated forest. -/
def extend (prefixIndex : ValueIndex (Accumulated Symbol)) (argument : Finite Symbol) : ValueIndex (Accumulated Symbol) :=
  ⟨convolve prefixIndex.counts argument.counts, fun position => do
    let pair ← productSplit prefixIndex.counts argument.counts position
    let before ← prefixIndex.select pair.1
    let after ← argument.select pair.2
    pure (before.1, before.2 ++ [after])⟩

/-- The term compiler's left fold uses the same prefix count for each argument. -/
def accumulate (prefixIndex : ValueIndex (Accumulated Symbol)) (arguments : List (Finite Symbol)) : ValueIndex (Accumulated Symbol) :=
  arguments.foldl extend prefixIndex

/-- The operation map does not change its successful rank interval. -/
theorem start_indexed (operation : Finite Symbol) (indexed : FiniteIndex operation) : Indexed (start operation) := by
  intro position
  constructor
  · rintro ⟨value, selected⟩
    obtain ⟨term, selected, _⟩ := Option.map_eq_some_iff.mp selected
    exact (indexed position).mp ⟨term, selected⟩
  · intro within
    obtain ⟨term, selected⟩ := (indexed position).mpr within
    exact ⟨(term, []), by simp [start, selected]⟩

/-- A source product selector covers exactly its count convolution. -/
theorem extend_indexed (prefixIndex : ValueIndex (Accumulated Symbol)) (argument : Finite Symbol)
    (partialIndexed : Indexed prefixIndex) (argumentIndexed : FiniteIndex argument) : Indexed (extend prefixIndex argument) := by
  intro position
  constructor
  · rintro ⟨value, selected⟩
    simp only [extend, bind, Option.bind_eq_some_iff] at selected
    obtain ⟨pair, split, before, first, after, second, _⟩ := selected
    have firstBound := (partialIndexed pair.1).mp ⟨before, first⟩
    have secondBound := (argumentIndexed pair.2).mp ⟨after, second⟩
    have recombined := productPosition_productSplit prefixIndex.counts argument.counts position pair.1 pair.2 split
    rw [← recombined]
    exact product_rank_bound _ _ _ _ firstBound secondBound
  · intro within
    obtain ⟨first, second, recombined, firstBound, secondBound⟩ := product_split _ _ position within
    obtain ⟨before, firstSelected⟩ := (partialIndexed first).mpr firstBound
    obtain ⟨after, secondSelected⟩ := (argumentIndexed second).mpr secondBound
    refine ⟨(before.1, before.2 ++ [after]), ?_⟩
    rw [← recombined]
    simp [extend, productSplit_productPosition _ _ _ _ firstBound secondBound, firstSelected, secondSelected]

/-- All arities, including no arguments, retain a complete finite selector per size. -/
theorem accumulate_indexed (prefixIndex : ValueIndex (Accumulated Symbol)) (arguments : List (Finite Symbol))
    (partialIndexed : Indexed prefixIndex) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument) :
    Indexed (accumulate prefixIndex arguments) := by
  induction arguments generalizing prefixIndex with
  | nil => exact partialIndexed
  | cons argument rest ih =>
      exact ih (extend prefixIndex argument)
        (extend_indexed prefixIndex argument partialIndexed (argumentsIndexed argument (by simp)))
        (fun child member => argumentsIndexed child (by simp [member]))

/-- A fixed request consumes one argument callback at each left-fold step. -/
def requestStep (state : ValueIndex (Accumulated Symbol) × List Checked)
    (request : Finite Symbol × EngineTerm Symbol) : ValueIndex (Accumulated Symbol) × List Checked :=
  (extend state.1 request.1,
    RecursiveCheckedRanks.productRows state.1.counts request.1.counts state.2 (request.1.positions .whole [request.2]))

/-- The callback product fold retains unchecked candidates and every operand order. -/
def requests (prefixIndex : ValueIndex (Accumulated Symbol)) (rows : List Checked)
    (arguments : List (Finite Symbol × EngineTerm Symbol)) : ValueIndex (Accumulated Symbol) × List Checked :=
  arguments.foldl requestStep (prefixIndex, rows)

/-- Callback accumulation uses exactly the independently constructed prefix index. -/
theorem requests_index (prefixIndex : ValueIndex (Accumulated Symbol)) (rows : List Checked)
    (arguments : List (Finite Symbol × EngineTerm Symbol)) :
    (requests prefixIndex rows arguments).1 = accumulate prefixIndex (arguments.map Prod.fst) := by
  induction arguments generalizing prefixIndex rows with
  | nil => rfl
  | cons argument rest ih =>
      simpa [requests, requestStep, accumulate] using ih (extend prefixIndex argument.1)
        (RecursiveCheckedRanks.productRows prefixIndex.counts argument.1.counts rows (argument.1.positions .whole [argument.2]))

/-- An exact candidate list for one accumulated payload. -/
def RowsExact (prefixIndex : ValueIndex (Accumulated Symbol)) (rows : List Checked) (wanted : Accumulated Symbol) : Prop :=
  ∀ position, (position, true) ∈ rows ↔ prefixIndex.select position = some wanted

/-- The complete child query is exact for its requested whole term. -/
def WholeExact (source : Finite Symbol) (wanted : EngineTerm Symbol) : Prop :=
  ∀ position, (position, true) ∈ source.positions .whole [wanted] ↔ source.select position = some wanted

/-- Full finite-field exactness supplies the child whole-term request law. -/
theorem whole_exact (source : Finite Symbol) (exact : FiniteExact source) (wanted : EngineTerm Symbol) :
    WholeExact source wanted := by
  intro position
  rw [exact]
  constructor
  · rintro ⟨term, selected, projected⟩
    have same := StaticCheckedRanks.whole_eq term wanted projected
    simpa [same] using selected
  · intro selected; exact ⟨wanted, selected, rfl⟩

/-- Appending one argument is injective in its previous payload and its new argument. -/
theorem payload_injective (first second : Accumulated Symbol) (left right : EngineTerm Symbol)
    (same : (first.1, first.2 ++ [left]) = (second.1, second.2 ++ [right])) : first = second ∧ left = right := by
  have op := congrArg Prod.fst same
  have children := List.append_inj' (congrArg Prod.snd same) rfl
  exact ⟨Prod.ext op children.1, (List.cons.inj children.2).1⟩

/-- The checked Cartesian callback is exact for the source append selector. -/
theorem extend_exact (prefixIndex : ValueIndex (Accumulated Symbol)) (argument : Finite Symbol)
    (partialIndexed : Indexed prefixIndex) (argumentIndexed : FiniteIndex argument)
    (rows : List Checked) (before : Accumulated Symbol) (after : EngineTerm Symbol)
    (rowsExact : RowsExact prefixIndex rows before) (argumentExact : WholeExact argument after) :
    RowsExact (extend prefixIndex argument)
      (RecursiveCheckedRanks.productRows prefixIndex.counts argument.counts rows (argument.positions .whole [after]))
      (before.1, before.2 ++ [after]) := by
  intro position
  constructor
  · intro member
    obtain ⟨first, second, firstMember, secondMember, rfl⟩ := product_origin _ _ _ _ _ member
    have firstSelected := (rowsExact first).mp firstMember
    have secondSelected := (argumentExact second).mp secondMember
    have firstBound := (partialIndexed first).mp ⟨before, firstSelected⟩
    have secondBound := (argumentIndexed second).mp ⟨after, secondSelected⟩
    simp [extend, productSplit_productPosition _ _ _ _ firstBound secondBound, firstSelected, secondSelected]
  · intro selected
    simp only [extend, bind, Option.bind_eq_some_iff] at selected
    obtain ⟨pair, split, actualBefore, firstSelected, actualAfter, secondSelected, result⟩ := selected
    have same := payload_injective actualBefore before actualAfter after (Option.some.inj result)
    rcases same with ⟨rfl, rfl⟩
    have firstMember := (rowsExact pair.1).mpr firstSelected
    have secondMember := (argumentExact pair.2).mpr secondSelected
    have combined := RecursiveCheckedRanks.product_complete prefixIndex.counts argument.counts _ _ _ _ firstMember secondMember
    simpa only [productPosition_productSplit _ _ position pair.1 pair.2 split] using combined

/-- The complete left-fold callback is exact for the selected operation and argument forest. -/
theorem requests_exact (prefixIndex : ValueIndex (Accumulated Symbol)) (rows : List Checked)
    (wanted : Accumulated Symbol) (arguments : List (Finite Symbol × EngineTerm Symbol))
    (partialIndexed : Indexed prefixIndex)
    (indexed : ∀ entry ∈ arguments, FiniteIndex entry.1)
    (exact : ∀ entry ∈ arguments, WholeExact entry.1 entry.2)
    (rowsExact : RowsExact prefixIndex rows wanted) :
    RowsExact (accumulate prefixIndex (arguments.map Prod.fst)) (requests prefixIndex rows arguments).2
      (wanted.1, wanted.2 ++ arguments.map Prod.snd) := by
  induction arguments generalizing prefixIndex rows wanted with
  | nil => simpa [accumulate, requests] using rowsExact
  | cons entry rest ih =>
      have nextIndexed := extend_indexed prefixIndex entry.1 partialIndexed (indexed entry (by simp))
      have nextExact := extend_exact prefixIndex entry.1 partialIndexed (indexed entry (by simp)) rows wanted entry.2
        rowsExact (exact entry (by simp))
      have tail := ih (extend prefixIndex entry.1)
        (RecursiveCheckedRanks.productRows prefixIndex.counts entry.1.counts rows (entry.1.positions .whole [entry.2]))
        (wanted.1, wanted.2 ++ [entry.2]) nextIndexed
        (fun child member => indexed child (by simp [member]))
        (fun child member => exact child (by simp [member])) nextExact
      simpa [requests, requestStep, accumulate, List.append_assoc] using tail

/-- All candidate rows are within their source class, regardless of the checked flag. -/
def Bounded (counts : Nat → Nat) (rows : List Checked) : Prop :=
  ∀ row ∈ rows, row.1.rank < counts row.1.size

/-- A checked Cartesian fold preserves bounds even for unchecked input candidates. -/
theorem product_bounded (left right : Nat → Nat) (first second : List Checked)
    (leftBounded : Bounded left first) (rightBounded : Bounded right second) :
    Bounded (convolve left right) (RecursiveCheckedRanks.productRows left right first second) := by
  intro row member
  obtain ⟨a, am, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨b, bm, rfl⟩ := List.mem_map.mp mapped
  exact product_rank_bound _ _ _ _ (leftBounded a am) (rightBounded b bm)

/-- The full source callback fold preserves every input interval bound. -/
theorem requests_bounded (prefixIndex : ValueIndex (Accumulated Symbol)) (rows : List Checked)
    (arguments : List (Finite Symbol × EngineTerm Symbol)) (bounded : Bounded prefixIndex.counts rows)
    (children : ∀ entry ∈ arguments, Bounded entry.1.counts (entry.1.positions .whole [entry.2])) :
    Bounded (accumulate prefixIndex (arguments.map Prod.fst)).counts (requests prefixIndex rows arguments).2 := by
  induction arguments generalizing prefixIndex rows with
  | nil => exact bounded
  | cons entry rest ih =>
      exact ih (extend prefixIndex entry.1) _
        (product_bounded _ _ _ _ bounded (children entry (by simp)))
        (fun child member => children child (by simp [member]))

/-- Distinct candidate positions survive every argument of the source fold. -/
theorem requests_distinct (prefixIndex : ValueIndex (Accumulated Symbol)) (rows : List Checked)
    (arguments : List (Finite Symbol × EngineTerm Symbol))
    (bounded : Bounded prefixIndex.counts rows) (distinct : Distinct rows)
    (childrenBounded : ∀ entry ∈ arguments, Bounded entry.1.counts (entry.1.positions .whole [entry.2]))
    (childrenDistinct : ∀ entry ∈ arguments, Distinct (entry.1.positions .whole [entry.2])) :
    Distinct (requests prefixIndex rows arguments).2 := by
  induction arguments generalizing prefixIndex rows with
  | nil => exact distinct
  | cons entry rest ih =>
      exact ih (extend prefixIndex entry.1) _
        (product_bounded _ _ _ _ bounded (childrenBounded entry (by simp)))
        (product_distinct _ _ _ _ distinct (childrenDistinct entry (by simp)) bounded (childrenBounded entry (by simp)))
        (fun child member => childrenBounded child (by simp [member]))
        (fun child member => childrenDistinct child (by simp [member]))

/-- The independent value-index scan records the count function before each argument. -/
def prefixCounts (initial : Nat → Nat) (arguments : List (Finite Symbol)) : List (Nat → Nat) :=
  arguments.scanl (fun counts argument => convolve counts argument.counts) initial

/-- Source zip3 pairs each argument query with its preceding scanned value count. -/
def scheduledRequests (initial : Nat → Nat) (rows : List Checked)
    (arguments : List (Finite Symbol)) (terms : List (EngineTerm Symbol)) : List Checked :=
  ((prefixCounts initial arguments).zip (arguments.zip terms)).foldl
    (fun prior entry => RecursiveCheckedRanks.productRows entry.1 entry.2.1.counts prior
      (entry.2.1.positions .whole [entry.2.2])) rows

/-- The fused callback fold equals the source scanl and zip3 schedule, even before an arity check. -/
theorem requests_schedule (prefixIndex : ValueIndex (Accumulated Symbol)) (rows : List Checked)
    (arguments : List (Finite Symbol)) (terms : List (EngineTerm Symbol)) :
    (requests prefixIndex rows (arguments.zip terms)).2 = scheduledRequests prefixIndex.counts rows arguments terms := by
  induction arguments generalizing prefixIndex rows terms with
  | nil => simp [requests, scheduledRequests]
  | cons argument rest ih =>
      cases terms with
      | nil => simp [requests, scheduledRequests]
      | cons term terms =>
          simpa [requests, requestStep, scheduledRequests, prefixCounts, extend] using
            ih (extend prefixIndex argument)
              (RecursiveCheckedRanks.productRows prefixIndex.counts argument.counts rows (argument.positions .whole [term])) terms

/-- A local selector preserves the accumulated forest length. -/
def LengthIs (index : ValueIndex (Accumulated Symbol)) (arity : Nat) : Prop :=
  ∀ position payload, index.select position = some payload → payload.2.length = arity

/-- The initial operation index has no arguments. -/
theorem start_length (operation : Finite Symbol) : LengthIs (start operation) 0 := by
  intro position payload selected
  obtain ⟨term, _, rfl⟩ := Option.map_eq_some_iff.mp selected
  rfl

/-- The product selector appends precisely one argument. -/
theorem extend_length (prefixIndex : ValueIndex (Accumulated Symbol)) (argument : Finite Symbol)
    (arity : Nat) (length : LengthIs prefixIndex arity) : LengthIs (extend prefixIndex argument) (arity + 1) := by
  intro position payload selected
  simp only [extend, bind, Option.bind_eq_some_iff] at selected
  obtain ⟨pair, _, before, first, after, _, result⟩ := selected
  have same := Option.some.inj result
  subst payload
  simp [length pair.1 before first]

/-- Every accumulated result has the declared number of argument terms. -/
theorem accumulate_length (prefixIndex : ValueIndex (Accumulated Symbol)) (arguments : List (Finite Symbol))
    (arity : Nat) (length : LengthIs prefixIndex arity) :
    LengthIs (accumulate prefixIndex arguments) (arity + arguments.length) := by
  induction arguments generalizing prefixIndex arity with
  | nil => simpa [accumulate] using length
  | cons argument rest ih =>
      simpa [accumulate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (extend prefixIndex argument) (arity + 1) (extend_length prefixIndex argument arity length)

/-- Key checking changes flags and retains all source positions. -/
def mask (checked : Bool) (rows : List Checked) : List Checked :=
  rows.map (fun row => (row.1, row.2 && checked))

/-- A masked certificate exists exactly when its key check and original certificate pass. -/
theorem mask_true (checked : Bool) (rows : List Checked) (position : Position) :
    (position, true) ∈ mask checked rows ↔ checked = true ∧ (position, true) ∈ rows := by
  cases checked <;> simp [mask]

/-- The source key check commutes with every subsequent checked Cartesian product. -/
theorem product_mask (checked : Bool) (left right : Nat → Nat) (first second : List Checked) :
    RecursiveCheckedRanks.productRows left right (mask checked first) second =
      mask checked (RecursiveCheckedRanks.productRows left right first second) := by
  simp only [RecursiveCheckedRanks.productRows, mask, List.flatMap_map, List.map_flatMap]
  congr 1
  funext row
  simp only [List.map_map]
  congr 1
  funext other
  dsimp only [Function.comp_def]
  cases row.2 <;> cases other.2 <;> cases checked <;> rfl

/-- The complete left-fold callback retains the independent key check. -/
theorem requests_mask (checked : Bool) (prefixIndex : ValueIndex (Accumulated Symbol))
    (rows : List Checked) (arguments : List (Finite Symbol × EngineTerm Symbol)) :
    (requests prefixIndex (mask checked rows) arguments).2 =
      mask checked (requests prefixIndex rows arguments).2 := by
  induction arguments generalizing prefixIndex rows with
  | nil => rfl
  | cons entry rest ih =>
      simp only [requests, List.foldl_cons, requestStep]
      rw [product_mask]
      exact ih (extend prefixIndex entry.1) _

/-- Key checking preserves every candidate's size interval. -/
theorem mask_bounded (checked : Bool) (counts : Nat → Nat) (rows : List Checked)
    (bounded : Bounded counts rows) : Bounded counts (mask checked rows) := by
  intro row member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact bounded original present

/-- Key checking preserves distinct source positions even when every flag becomes false. -/
theorem mask_distinct (checked : Bool) (rows : List Checked) (distinct : Distinct rows) :
    Distinct (mask checked rows) := by
  rw [distinct_iff] at distinct ⊢
  simpa [mask, List.map_map, Function.comp_def] using distinct

end MicroCFTA.RecursiveJoinFields
