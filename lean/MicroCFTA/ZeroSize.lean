import MicroCFTA.Probability

/-!
# Zero-size components and integer-point closure

Finite size-split selection must admit a left size equal to the total when
the right side has size zero. Integer-point closure adds one source choice
per variable. These proofs cover finite lists and ranked closure. They do not
establish productivity of a lazy recursive Haskell knot or lattice counting.
-/

namespace MicroCFTA.ZeroSize

/-- A sparse class contains a natural size and a natural member count. -/
abbrev Cell := Nat × Nat

/-- The size keys of a finite sparse list do not decrease. -/
def Ordered (entries : List Cell) : Prop :=
  entries.Pairwise (fun left right => left.1 ≤ right.1)

/-- The exclusive operation-size limit used by `productSplitSizes`. -/
def splitLimit (right : List Cell) (total : Nat) : Nat :=
  match right with
  | (0, _) :: _ => total + 1
  | _ => total

/-- Candidate operation classes, before zero-width blocks are skipped. -/
def splitCandidates (left right : List Cell) (total : Nat) : List Cell :=
  left.takeWhile (fun entry => decide (entry.1 < splitLimit right total))

/-- Every actual pair of sizes passes the corrected candidate limit. -/
theorem pair_passes_limit (right : List Cell) (ordered : Ordered right)
    (entry : Cell) (member : entry ∈ right) (left total : Nat)
    (sum : left + entry.1 = total) : left < splitLimit right total := by
  cases right with
  | nil => simp at member
  | cons head tail =>
      rcases head with ⟨size, count⟩
      cases size with
      | zero => simp only [splitLimit]; omega
      | succ size =>
          have lower : size + 1 ≤ entry.1 := by
            rcases List.mem_cons.mp member with same | inside
            · subst entry
              exact Nat.le_refl _
            · exact (List.pairwise_cons.mp ordered).1 entry inside
          simp only [splitLimit]
          omega

/-- For an ordered list, a prefix size limit is exactly a membership restriction. -/
theorem mem_takeWhile_size (entries : List Cell) (ordered : Ordered entries)
    (limit : Nat) (entry : Cell) :
    entry ∈ entries.takeWhile (fun cell => decide (cell.1 < limit)) ↔
      entry ∈ entries ∧ entry.1 < limit := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp ordered
      by_cases fits : head.1 < limit
      · simp only [List.takeWhile_cons, fits, decide_true, ↓reduceIte, List.mem_cons]
        rw [ih parts.2]
        constructor
        · rintro (rfl | ⟨inside, bound⟩)
          · exact ⟨Or.inl rfl, fits⟩
          · exact ⟨Or.inr inside, bound⟩
        · rintro ⟨same | inside, bound⟩
          · exact Or.inl same
          · exact Or.inr ⟨inside, bound⟩
      · simp only [List.takeWhile_cons, fits, decide_false, Bool.false_eq_true,
          ↓reduceIte, List.not_mem_nil, false_iff, not_and]
        intro member bound
        have lower : head.1 ≤ entry.1 := by
          rcases List.mem_cons.mp member with same | inside
          · subst entry
            exact Nat.le_refl _
          · exact parts.1 entry inside
        omega

/-- No size pair is lost, including a pair with a zero-size component. -/
theorem splitCandidates_complete (left right : List Cell)
    (orderedLeft : Ordered left) (orderedRight : Ordered right)
    (l r : Cell) (hl : l ∈ left) (hr : r ∈ right) (total : Nat)
    (sum : l.1 + r.1 = total) : l ∈ splitCandidates left right total :=
  (mem_takeWhile_size left orderedLeft _ l).mpr
    ⟨hl, pair_passes_limit right orderedRight r hr l.1 total sum⟩

/-- A candidate never asks for a negative right-hand size. -/
theorem splitCandidates_bound (left right : List Cell) (ordered : Ordered left)
    (total : Nat) (entry : Cell) (member : entry ∈ splitCandidates left right total) :
    entry.1 ≤ total := by
  have bound := ((mem_takeWhile_size left ordered _ entry).mp member).2
  cases right with
  | nil => simp [splitLimit] at bound; omega
  | cons head tail =>
      rcases head with ⟨size, count⟩
      cases size <;> simp [splitLimit] at bound <;> omega

/-- Truncating an ordered list preserves a flat map whose outputs require the limit. -/
theorem flatMap_takeWhile_size {Value : Type} (entries : List Cell)
    (ordered : Ordered entries) (limit : Nat) (outputs : Cell → List Value)
    (relevant : ∀ entry, entry ∈ entries → outputs entry ≠ [] → entry.1 < limit) :
    (entries.takeWhile (fun entry => decide (entry.1 < limit))).flatMap outputs =
      entries.flatMap outputs := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp ordered
      by_cases fits : head.1 < limit
      · simp only [List.takeWhile_cons, fits, decide_true, ↓reduceIte, List.flatMap_cons]
        rw [ih parts.2 (fun entry member => relevant entry (List.mem_cons_of_mem _ member))]
      · have empty : (head :: tail).flatMap outputs = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro entry member
          apply Classical.byContradiction
          intro nonempty
          have upper := relevant entry member nonempty
          have lower : head.1 ≤ entry.1 := by
            rcases List.mem_cons.mp member with same | inside
            · subst entry
              exact Nat.le_refl _
            · exact parts.1 entry inside
          omega
        simp [fits, empty]

/-- All right-hand partners with the requested sum, in their original order. -/
def partners (right : List Cell) (total : Nat) (left : Cell) : List (Cell × Cell) :=
  (right.filter fun r => decide (left.1 + r.1 = total)).map fun r => (left, r)

/-- The optimized candidate prefix preserves the complete ordered pair list.
This equality preserves duplicate occurrences as well as membership. -/
theorem splitPairs_exact (left right : List Cell)
    (orderedLeft : Ordered left) (orderedRight : Ordered right) (total : Nat) :
    (splitCandidates left right total).flatMap (partners right total) =
      left.flatMap (partners right total) := by
  apply flatMap_takeWhile_size left orderedLeft _ (partners right total)
  intro entry _ nonempty
  have existsPartner : ∃ r, r ∈ right ∧ entry.1 + r.1 = total := by
    apply Classical.byContradiction
    intro absent
    apply nonempty
    have noPartners : right.filter (fun r => decide (entry.1 + r.1 = total)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro r member equation
      exact absent ⟨r, member, of_decide_eq_true equation⟩
    simp [partners, noPartners]
  obtain ⟨r, member, sum⟩ := existsPartner
  exact pair_passes_limit right orderedRight r member entry.1 total sum

/-- A zero-size right component requires the boundary operation-size candidate. -/
theorem zero_right_boundary (size leftCount rightCount : Nat) :
    splitCandidates [(size, leftCount)] [(0, rightCount)] size = [(size, leftCount)] := by
  simp [splitCandidates, splitLimit]

/-- The former strict-total limit deletes that valid boundary candidate. -/
theorem strict_limit_loses_zero_right (size count : Nat) :
    ([(size, count)] : List Cell).takeWhile (fun entry => decide (entry.1 < size)) = [] := by
  simp

/-- Zero-sized pairing machinery contributes no source choices. -/
theorem zero_pairing_size (left right : Nat) : 0 + left + right = left + right := by
  omega

/-- The size of a finite integer tuple is one choice per variable. -/
def pointSize (variables : Nat) : Nat :=
  ((List.finRange variables).map fun _ => (1 : Nat)).sum

/-- Closing a tuple adds its variable count, including zero variables. -/
theorem pointSize_eq (variables : Nat) : pointSize variables = variables := by
  have ones {α : Type} (xs : List α) : (xs.map fun _ => (1 : Nat)).sum = xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.add_comm]
  simpa [pointSize] using ones (List.finRange variables)

/-- A finite indexed table of integer tuples. The lattice implementation supplies it. -/
structure Points (variables : Nat) where
  count : Nat
  decode : Fin count → (Fin variables → Int)

/-- Each open source outcome has a size and a function of the integer tuple. -/
abbrev OpenOutcome (variables : Nat) (Value : Type) := Nat × ((Fin variables → Int) → Value)

/-- Materialize all source-outcome and integer-point combinations. -/
def closePoints {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value)) : List (Nat × Value) :=
  sources.flatMap fun source =>
    (List.finRange points.count).map fun rank =>
      (source.1 + pointSize variables, source.2 (points.decode rank))

/-- Concrete finite closure retains exactly the source/point combinations. -/
theorem mem_closePoints {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value))
    (size : Nat) (value : Value) :
    (size, value) ∈ closePoints points sources ↔
      ∃ source, source ∈ sources ∧ ∃ rank : Fin points.count,
        size = source.1 + variables ∧ value = source.2 (points.decode rank) := by
  simp only [closePoints, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
    Prod.mk.injEq, pointSize_eq]
  constructor
  · rintro ⟨source, member, rank, hs, hv⟩
    exact ⟨source, member, rank, hs.symm, hv.symm⟩
  · rintro ⟨source, member, rank, hs, hv⟩
    exact ⟨source, member, rank, hs.symm, hv.symm⟩

/-- Closing integer tuples multiplies the finite replay cardinalities. -/
theorem closePoints_length {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value)) :
    (closePoints points sources).length = sources.length * points.count := by
  induction sources with
  | nil => simp [closePoints]
  | cons source rest ih =>
      simp only [closePoints, List.flatMap_cons, List.length_append, List.length_map,
        List.length_finRange] at *
      rw [ih]
      simp [Nat.add_mul, Nat.add_comm]

/-- An exact point table represents each valid tuple at exactly one rank. -/
def ExactPoints {variables : Nat} (points : Points variables)
    (valid : (Fin variables → Int) → Prop) : Prop :=
  (∀ tuple, valid tuple ↔ ∃ rank, points.decode rank = tuple) ∧
    Function.Injective points.decode

/-- Exact input points give sound and complete finite closure.
Only the lattice result is assumed exact; the source/point combination is proved here. -/
theorem closePoints_exact {Value : Type} {variables : Nat}
    (points : Points variables) (valid : (Fin variables → Int) → Prop)
    (exactPoints : ExactPoints points valid) (sources : List (OpenOutcome variables Value))
    (size : Nat) (value : Value) :
    (size, value) ∈ closePoints points sources ↔
      ∃ source, source ∈ sources ∧ ∃ tuple, valid tuple ∧
        size = source.1 + variables ∧ value = source.2 tuple := by
  rw [mem_closePoints]
  constructor
  · rintro ⟨source, member, rank, hs, hv⟩
    exact ⟨source, member, points.decode rank,
      (exactPoints.1 _).mpr ⟨rank, rfl⟩, hs, hv⟩
  · rintro ⟨source, member, tuple, validTuple, hs, hv⟩
    obtain ⟨rank, rfl⟩ := (exactPoints.1 tuple).mp validTuple
    exact ⟨source, member, rank, hs, hv⟩

/-- An exact integer-point table has one and only one rank for each valid tuple. -/
theorem point_unique_rank {variables : Nat} (points : Points variables)
    (valid : (Fin variables → Int) → Prop) (exactPoints : ExactPoints points valid)
    (tuple : Fin variables → Int) :
    valid tuple ↔ ∃ rank, points.decode rank = tuple ∧
      ∀ other, points.decode other = tuple → other = rank := by
  constructor
  · intro accepted
    obtain ⟨rank, same⟩ := (exactPoints.1 tuple).mp accepted
    refine ⟨rank, same, ?_⟩
    intro other equal
    exact exactPoints.2 (equal.trans same.symm)
  · rintro ⟨rank, same, _⟩
    exact (exactPoints.1 tuple).mpr ⟨rank, same⟩

/-- With no integer variables, an exact table contains at most the empty tuple. -/
theorem zero_variable_point_count (points : Points 0)
    (valid : (Fin 0 → Int) → Prop) (exactPoints : ExactPoints points valid) :
    points.count ≤ 1 := by
  by_cases small : points.count ≤ 1
  · exact small
  · have two : 1 < points.count := by omega
    have zero : 0 < points.count := by omega
    have tuples : points.decode ⟨0, zero⟩ = points.decode ⟨1, two⟩ := by
      funext coordinate
      exact Fin.elim0 coordinate
    have ranks := congrArg Fin.val (exactPoints.2 tuples)
    simp at ranks

/-- Encode a source rank and a point rank in source-major order. -/
def closureRank {sourceCount pointCount : Nat}
    (source : Fin sourceCount) (point : Fin pointCount) : Fin (sourceCount * pointCount) :=
  ⟨Probability.pairRank pointCount source.val point.val,
    Probability.pairRank_lt source.isLt point.isLt⟩

/-- Decode a finite closure rank into its source and point ranks. -/
def closureParts {sourceCount pointCount : Nat} (rank : Fin (sourceCount * pointCount)) :
    Fin sourceCount × Fin pointCount :=
  let parts := Probability.splitRank pointCount rank.val
  let bounds := Probability.split_lt rank.isLt
  (⟨parts.1, bounds.1⟩, ⟨parts.2, bounds.2⟩)

/-- Every encoded source/point pair decodes to the same pair. -/
theorem closureParts_rank {sourceCount pointCount : Nat}
    (source : Fin sourceCount) (point : Fin pointCount) :
    closureParts (closureRank source point) = (source, point) := by
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst (Probability.split_pair point.isLt)
  · exact congrArg Prod.snd (Probability.split_pair point.isLt)

/-- Every finite closure rank is the encoding of its decoded parts. -/
theorem closureRank_parts {sourceCount pointCount : Nat}
    (rank : Fin (sourceCount * pointCount)) :
    closureRank (closureParts rank).1 (closureParts rank).2 = rank := by
  apply Fin.ext
  exact Probability.pair_split pointCount rank.val

/-- Select the size and value of one concrete finite closure rank. -/
def closureSelect {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value))
    (rank : Fin (sources.length * points.count)) : Nat × Value :=
  let parts := closureParts rank
  let source := sources[parts.1.val]
  (source.1 + variables, source.2 (points.decode parts.2))

/-- Rank replay uses the chosen source, the chosen integer tuple, and all variable sizes. -/
theorem closureSelect_rank {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value))
    (source : Fin sources.length) (point : Fin points.count) :
    closureSelect points sources (closureRank source point) =
      (sources[source.val].1 + variables, sources[source.val].2 (points.decode point)) := by
  simp [closureSelect, closureParts_rank]

/-- Every finite replay rank returns one of the materialized closure outcomes. -/
theorem closureSelect_mem {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value))
    (rank : Fin (sources.length * points.count)) :
    closureSelect points sources rank ∈ closePoints points sources := by
  apply (mem_closePoints points sources _ _).mpr
  exact ⟨sources[(closureParts rank).1.val],
    List.getElem_mem (closureParts rank).1.isLt, (closureParts rank).2, rfl, rfl⟩

/-- Every materialized closure outcome has a valid replay rank. -/
theorem closePoints_has_rank {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value))
    (size : Nat) (value : Value) :
    (size, value) ∈ closePoints points sources ↔
      ∃ rank : Fin (sources.length * points.count), closureSelect points sources rank = (size, value) := by
  constructor
  · intro member
    obtain ⟨source, inside, point, hs, hv⟩ := (mem_closePoints points sources size value).mp member
    obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp inside
    refine ⟨closureRank ⟨index, bound⟩ point, ?_⟩
    rw [closureSelect_rank]
    simp only [same, hs, hv]
  · rintro ⟨rank, same⟩
    rw [← same]
    exact closureSelect_mem points sources rank

/-- Every size class shifts by the variable count and multiplies by the point count. -/
theorem closePoints_size_count {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value)) (size : Nat) :
    (closePoints points sources).countP (fun outcome => decide (outcome.1 = size + variables)) =
      sources.countP (fun source => decide (source.1 = size)) * points.count := by
  induction sources with
  | nil => simp [closePoints]
  | cons source rest ih =>
      simp only [closePoints, List.flatMap_cons, List.countP_append,
        List.countP_map, Function.comp_def, pointSize_eq, Nat.add_right_cancel_iff]
      simp only [closePoints, pointSize_eq] at ih
      rw [ih, List.countP_cons]
      by_cases same : source.1 = size
      · simp [same, List.countP_true, Nat.add_mul, Nat.add_comm]
      · simp [same, List.countP_false]

/-- No closed outcome has a size below the number of chosen integers. -/
theorem closePoints_minimum {Value : Type} {variables : Nat}
    (points : Points variables) (sources : List (OpenOutcome variables Value))
    (size : Nat) (value : Value) (member : (size, value) ∈ closePoints points sources) :
    variables ≤ size := by
  obtain ⟨source, _, _, hs, _⟩ := (mem_closePoints points sources size value).mp member
  omega

/-- Closing disjoint variable groups adds the same size as closing their combined tuple. -/
theorem closure_size_additive (base leftVariables rightVariables : Nat) :
    base + pointSize leftVariables + pointSize rightVariables =
      base + pointSize (leftVariables + rightVariables) := by
  simp [pointSize_eq, Nat.add_assoc]

/-- A product decreases the recursive size only when its other component is positive. -/
theorem product_strictly_decreases_iff (recursiveSize otherSize : Nat) :
    recursiveSize < recursiveSize + otherSize ↔ 0 < otherSize := by
  omega

/-- A zero-size component does not guard a recursive occurrence by size. -/
theorem zero_size_does_not_guard (recursiveSize : Nat) :
    ¬recursiveSize < recursiveSize + 0 := by
  omega

/-- A seeded same-size recurrence with at least one recursive copy has no finite count.
Such a recurrence cannot be justified by a finite size-class sampler. -/
theorem zero_lag_no_finite_count (seed copies count : Nat)
    (positiveSeed : 0 < seed) (hasCopy : 1 ≤ copies) :
    count ≠ seed + copies * count := by
  intro equation
  have grows : count ≤ copies * count := by
    simpa using Nat.mul_le_mul_right count hasCopy
  omega

/-- Lookup in an ascending sparse count list, as in `valueAtSize`. -/
def firstCountAt (entries : List Cell) (wanted : Nat) : Nat :=
  match entries.dropWhile (fun entry => decide (entry.1 < wanted)) with
  | (size, count) :: _ => if size = wanted then count else 0
  | [] => 0

/-- A size-one sentinel before a size-zero product hides every member at size zero. -/
theorem one_sentinel_hides_zero_product (count : Nat) :
    firstCountAt [(1, 0), (0, count)] 0 = 0 := by
  simp [firstCountAt]

/-- A size-one sentinel before a size-one product also hides every actual member. -/
theorem one_sentinel_hides_one_product (count : Nat) :
    firstCountAt [(1, 0), (1, count)] 1 = 0 := by
  simp [firstCountAt]

end MicroCFTA.ZeroSize
