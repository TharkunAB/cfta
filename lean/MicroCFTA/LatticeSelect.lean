import MicroCFTA.CoreLattice
import MicroCFTA.FullSyntax
import MicroCFTA.LatticeAPI
import MicroCFTA.LatticeCumulative
import MicroCFTA.SearchCost

/-!
# Polynomial counts and finite coordinate selection

A successful elimination supplies a finite support witness for the next
coordinate. Its completion values are natural numbers because the initial
pieces denote the formula's indicator. This module derives a finite section
table from those values and proves that the actual cumulative polynomials
compute the same counts. The table is a proof witness, not an enumeration
step in the polynomial decoder.
-/

namespace MicroCFTA.LatticeSelect

open LatticePiece LatticePipeline LatticeCount LatticeLevels

/-- Convert an exact nonnegative rational integer to a natural count. -/
def naturalCount (value : Rat) : Nat := value.num.toNat

/-- Natural-count conversion is exact whenever the value is a natural integer. -/
theorem naturalCount_exact (value : Rat) (natural : ∃ count : Nat, value = (count : Rat)) :
    (naturalCount value : Rat) = value := by
  obtain ⟨count, rfl⟩ := natural
  simp [naturalCount]

/-- Attach the actual completion count to each coordinate in a finite support witness. -/
def coordinateTable (support : List Int) (value : Int → Rat) : List (LatticeRank.Section Nat) :=
  support.map fun coordinate => (coordinate, naturalCount (value coordinate))

/-- A duplicate-free support witness gives unique section keys. -/
theorem coordinateTable_unique (support : List Int) (value : Int → Rat)
    (unique : support.Nodup) : LatticeRank.UniqueCoordinates (coordinateTable support value) := by
  simpa [LatticeRank.UniqueCoordinates, coordinateTable, List.pairwise_map, List.Nodup] using unique

/-- The finite table total is the rational sum of its actual completion values. -/
theorem coordinateTable_total (support : List Int) (value : Int → Rat)
    (natural : ∀ coordinate, ∃ count : Nat, value coordinate = (count : Rat)) :
    (LatticeRank.sectionTotal id (coordinateTable support value) : Rat) =
      FiniteSum.listSum support value := by
  induction support with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [coordinateTable] at ih
      simp [coordinateTable, LatticeRank.sectionTotal, FiniteSum.listSum,
        Rat.natCast_add, ih, naturalCount_exact _ (natural coordinate)]

/-- Table cumulative counts are the finite sum restricted by the coordinate bound. -/
theorem coordinateTable_through (support : List Int) (value : Int → Rat)
    (natural : ∀ coordinate, ∃ count : Nat, value coordinate = (count : Rat)) (bound : Int) :
    (LatticeRank.through id (coordinateTable support value) bound : Rat) =
      FiniteSum.listSum support (fun coordinate => if coordinate ≤ bound then value coordinate else 0) := by
  induction support with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [coordinateTable] at ih
      by_cases below : coordinate ≤ bound <;>
        simp [coordinateTable, LatticeRank.through, FiniteSum.listSum, below,
          Rat.natCast_add, Rat.zero_add, ih, naturalCount_exact _ (natural coordinate)]

/-- A table's count at one coordinate is a Kronecker sum over its support. -/
theorem coordinateTable_at (support : List Int) (value : Int → Rat)
    (natural : ∀ coordinate, ∃ count : Nat, value coordinate = (count : Rat)) (selected : Int) :
    (LatticeRank.atCoordinate id (coordinateTable support value) selected : Rat) =
      FiniteSum.listSum support (fun coordinate => if coordinate = selected then value selected else 0) := by
  induction support with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [coordinateTable] at ih
      by_cases same : coordinate = selected
      · subst coordinate
        simp [coordinateTable, LatticeRank.atCoordinate, FiniteSum.listSum,
          Rat.natCast_add, ih, naturalCount_exact _ (natural selected)]
      · simp [coordinateTable, LatticeRank.atCoordinate, FiniteSum.listSum, same,
          ih, Rat.zero_add]

/-- A complete support witness gives the exact count at every integer coordinate. -/
theorem coordinateTable_at_exact (support : List Int) (value : Int → Rat)
    (unique : support.Nodup) (covers : ∀ coordinate, value coordinate ≠ 0 → coordinate ∈ support)
    (natural : ∀ coordinate, ∃ count : Nat, value coordinate = (count : Rat)) (selected : Int) :
    (LatticeRank.atCoordinate id (coordinateTable support value) selected : Rat) = value selected := by
  rw [coordinateTable_at support value natural selected,
    FiniteSum.listSum_delta support unique value covers selected]

/-- The completion function at the next stored level after one coordinate update. -/
def completions (levels : List (List Piece)) (index : Nat) (assignment : Nat → Int)
    (coordinate : Int) : Rat :=
  total (levels.getD (index + 1) []) (LatticeBound.update assignment index coordinate)

/-- The actual polynomial cumulative function for a stored level and prefix. -/
def cumulative (levels : List (List Piece)) (index : Nat) (assignment : Nat → Int)
    (bound : Int) : Rat :=
  LatticeCumulative.through index
    (LatticeCumulative.cumulativePieces levels index (prefixValues assignment index)) bound

/-- Every compiled core formula starts with a natural zero-or-one count at each assignment. -/
theorem initial_natural (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled) :
    ∀ assignment, ∃ count : Nat, total (LatticeInput.initial compiled) assignment = (count : Rat) := by
  intro assignment
  rw [LatticeInput.initial_total,
    CoreLattice.signed_indicator (LatticeInput.variableOf names)
      (LatticeInput.nameValues names assignment) assignment
      (LatticeInput.nameValues_correct names assignment) formula compiled parsed]
  cases CoreFormula.evalFormula (LatticeInput.nameValues names assignment) formula
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- Parsed core formulas use no coordinate outside their declared name list. -/
theorem initial_outside (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled) :
    ∀ index, names.length ≤ index → ∀ piece ∈ LatticeInput.initial compiled, FreePiece index piece := by
  intro index outside
  rcases LatticeInput.initial_covers names (CoreLattice.lowerFormula formula) compiled parsed index with
    occurs | absent
  · simp only [List.mem_reverse, List.mem_range] at occurs
    omega
  · exact absent

/-- Successful core compilation gives a finite coordinate table with exact polynomial cumulative counts. -/
theorem compiled_coordinate_table (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int) :
    ∃ table : List (LatticeRank.Section Nat),
      LatticeRank.UniqueCoordinates table ∧
      (LatticeRank.sectionTotal id table : Rat) = total (levels.getD index []) assignment ∧
      (∀ bound, (LatticeRank.through id table bound : Rat) = cumulative levels index assignment bound) ∧
      (∀ coordinate, (LatticeRank.atCoordinate id table coordinate : Rat) =
        completions levels index assignment coordinate) := by
  have natural := buildLevels_natural names.length (LatticeInput.initial compiled)
    (LatticeInput.initial_valid compiled) (initial_natural names formula compiled parsed)
    levels built (index + 1) (by omega)
  have summed := buildLevels_sum names.length (LatticeInput.initial compiled)
    (LatticeInput.initial_valid compiled) levels built index inside assignment
  obtain ⟨support, unique, covers, totalEq⟩ := summed
  let value := completions levels index assignment
  refine ⟨coordinateTable support value, coordinateTable_unique support value unique, ?_, ?_, ?_⟩
  · rw [coordinateTable_total support value (fun coordinate => natural _)]
    exact totalEq
  · intro bound
    rw [coordinateTable_through support value (fun coordinate => natural _) bound]
    apply FiniteSum.of_cover
      (LatticeCumulative.through_correct names.length (LatticeInput.initial compiled)
        (LatticeInput.initial_valid compiled) (initial_outside names formula compiled parsed)
        levels built index inside assignment bound) support unique
    intro coordinate nonzero
    by_cases below : coordinate ≤ bound
    · exact covers coordinate (by simpa [below] using nonzero)
    · simp [below] at nonzero
  · exact coordinateTable_at_exact support value unique covers (fun coordinate => natural _)

/-- The actual cumulative polynomial is nonnegative and integral at every bound. -/
theorem cumulative_natural (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int) (bound : Int) :
    ∃ count : Nat, cumulative levels index assignment bound = (count : Rat) := by
  obtain ⟨table, _, _, through, _⟩ :=
    compiled_coordinate_table names formula compiled parsed levels built index inside assignment
  exact ⟨LatticeRank.through id table bound, (through bound).symm⟩

/-- Cumulative monotonicity follows from compiled formula counts, not a search premise. -/
theorem cumulative_monotone (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int)
    (low high : Int) (ordered : low ≤ high) :
    cumulative levels index assignment low ≤ cumulative levels index assignment high := by
  obtain ⟨table, _, _, through, _⟩ :=
    compiled_coordinate_table names formula compiled parsed levels built index inside assignment
  rw [← through low, ← through high, Rat.natCast_le_natCast]
  exact LatticeRank.through_monotone id table low high ordered

/-- Read the source minimum lower endpoint and maximum upper endpoint. -/
def sourceBounds : List LatticeCumulative.CumulativePiece → Option (Int × Int)
  | [] => none
  | piece :: rest =>
      some (match sourceBounds rest with
        | none => (piece.low, piece.high)
        | some (low, high) => (min piece.low low, max piece.high high))

/-- The source bound extraction is defined exactly for a nonempty piece list. -/
theorem sourceBounds_none (pieces : List LatticeCumulative.CumulativePiece) :
    sourceBounds pieces = none ↔ pieces = [] := by
  cases pieces <;> simp [sourceBounds]

/-- Every cumulative interval is enclosed by the source minimum and maximum. -/
theorem sourceBounds_member (pieces : List LatticeCumulative.CumulativePiece) (low high : Int)
    (found : sourceBounds pieces = some (low, high))
    (piece : LatticeCumulative.CumulativePiece) (member : piece ∈ pieces) :
    low ≤ piece.low ∧ piece.high ≤ high := by
  induction pieces generalizing low high with
  | nil => simp at member
  | cons first rest ih =>
      cases tail : sourceBounds rest with
      | none =>
          have empty := (sourceBounds_none rest).mp tail
          subst rest
          simp [sourceBounds] at found
          rcases found with ⟨rfl, rfl⟩
          have same := List.mem_singleton.mp member
          subst piece
          exact ⟨Int.le_refl _, Int.le_refl _⟩
      | some bounds =>
          rcases bounds with ⟨lower, upper⟩
          simp [sourceBounds, tail] at found
          cases found
          rcases List.mem_cons.mp member with rfl | member
          · omega
          · have previous := ih lower upper tail member
            omega

/-- A nonzero finite list sum has a nonzero summand. -/
theorem listSum_nonzero (items : List α) (value : α → Rat)
    (nonzero : FiniteSum.listSum items value ≠ 0) :
    ∃ item ∈ items, value item ≠ 0 := by
  induction items with
  | nil => exact False.elim (nonzero rfl)
  | cons first rest ih =>
      by_cases head : value first = 0
      · have tail : FiniteSum.listSum rest value ≠ 0 := by
          simpa [FiniteSum.listSum, head, Rat.zero_add] using nonzero
        obtain ⟨item, member, present⟩ := ih tail
        exact ⟨item, by simp [member], present⟩
      · exact ⟨first, by simp, head⟩

/-- Every live completion lies in an actual generated cumulative interval. -/
theorem completion_interval (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int) (coordinate : Int)
    (nonzero : completions levels index assignment coordinate ≠ 0) :
    ∃ interval ∈ LatticeCumulative.cumulativePieces levels index (prefixValues assignment index),
      interval.low ≤ coordinate ∧ coordinate ≤ interval.high := by
  obtain ⟨piece, member, live⟩ := listSum_nonzero (levels.getD (index + 1) [])
    (fun piece => pieceValue (LatticeBound.update assignment index coordinate) piece) nonzero
  have accepted : holds (LatticeBound.update assignment index coordinate) piece.constraints = true := by
    cases h : holds (LatticeBound.update assignment index coordinate) piece.constraints
    · simp [pieceValue, h] at live
    · rfl
  cases found : LatticeInterval.intervalWithPrefix index (prefixValues assignment index) piece.constraints with
  | none =>
      have absent := buildLevels_interval_none names.length (LatticeInput.initial compiled)
        (LatticeInput.initial_valid compiled) (initial_outside names formula compiled parsed)
        levels built index inside assignment piece member found coordinate
      exact False.elim (live absent)
  | some endpoints =>
      rcases endpoints with ⟨low, high⟩
      have bounds := (buildLevels_interval_correct names.length (LatticeInput.initial compiled)
        (LatticeInput.initial_valid compiled) (initial_outside names formula compiled parsed)
        levels built index inside assignment piece member low high found coordinate).mp accepted
      refine ⟨⟨low, high, LatticeCumulative.cumulativePolynomial index (prefixValues assignment index) low piece.polynomial⟩,
        ?_, bounds⟩
      apply List.mem_filterMap.mpr
      exact ⟨piece, member, by simp [LatticeCumulative.cumulativePiece, found]⟩

/-- The source extrema enclose all coordinates with nonzero completion counts. -/
theorem sourceBounds_cover (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int) (low high : Int)
    (found : sourceBounds (LatticeCumulative.cumulativePieces levels index (prefixValues assignment index)) = some (low, high)) :
    ∀ coordinate, completions levels index assignment coordinate ≠ 0 → low ≤ coordinate ∧ coordinate ≤ high := by
  intro coordinate nonzero
  obtain ⟨piece, member, contains⟩ :=
    completion_interval names formula compiled parsed levels built index inside assignment coordinate nonzero
  have outer := sourceBounds_member _ low high found piece member
  omega

/-- A live prefix makes the source partial minimum and maximum operations safe. -/
theorem sourceBounds_exists (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int)
    (live : total (levels.getD index []) assignment ≠ 0) :
    ∃ low high, sourceBounds (LatticeCumulative.cumulativePieces levels index (prefixValues assignment index)) = some (low, high) ∧
      low ≤ high := by
  obtain ⟨support, _, _, totalEq⟩ := buildLevels_sum names.length (LatticeInput.initial compiled)
    (LatticeInput.initial_valid compiled) levels built index inside assignment
  obtain ⟨coordinate, _, nonzero⟩ := listSum_nonzero support _ (by rwa [totalEq])
  obtain ⟨piece, member, contains⟩ :=
    completion_interval names formula compiled parsed levels built index inside assignment coordinate nonzero
  cases found : sourceBounds (LatticeCumulative.cumulativePieces levels index (prefixValues assignment index)) with
  | none =>
      have empty := (sourceBounds_none _).mp found
      rw [empty] at member
      cases member
  | some endpoints =>
      rcases endpoints with ⟨low, high⟩
      have outer := sourceBounds_member _ low high found piece member
      exact ⟨low, high, rfl, by omega⟩

/-- No completion occurs below the source minimum bound. -/
theorem cumulative_before (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int) (low high : Int)
    (found : sourceBounds (LatticeCumulative.cumulativePieces levels index (prefixValues assignment index)) = some (low, high)) :
    cumulative levels index assignment (low - 1) = 0 := by
  have counted := LatticeCumulative.through_correct names.length (LatticeInput.initial compiled)
    (LatticeInput.initial_valid compiled) (initial_outside names formula compiled parsed)
    levels built index inside assignment (low - 1)
  apply FiniteSum.unique counted
  apply FiniteSum.congr FiniteSum.zero
  intro coordinate
  by_cases below : coordinate ≤ low - 1
  · have zero : completions levels index assignment coordinate = 0 := by
      by_cases zero : completions levels index assignment coordinate = 0
      · exact zero
      · exfalso
        have bounds := sourceBounds_cover names formula compiled parsed levels built index inside assignment low high found coordinate zero
        omega
    simpa [below, completions] using zero.symm
  · simp [below]

/-- The source maximum includes every completion of the current prefix. -/
theorem cumulative_after (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int) (low high : Int)
    (found : sourceBounds (LatticeCumulative.cumulativePieces levels index (prefixValues assignment index)) = some (low, high)) :
    cumulative levels index assignment high = total (levels.getD index []) assignment := by
  have counted := LatticeCumulative.through_correct names.length (LatticeInput.initial compiled)
    (LatticeInput.initial_valid compiled) (initial_outside names formula compiled parsed)
    levels built index inside assignment high
  apply FiniteSum.unique counted
  apply FiniteSum.congr (buildLevels_sum names.length (LatticeInput.initial compiled)
    (LatticeInput.initial_valid compiled) levels built index inside assignment)
  intro coordinate
  by_cases below : coordinate ≤ high
  · simp [below]
  · have zero : completions levels index assignment coordinate = 0 := by
      by_cases zero : completions levels index assignment coordinate = 0
      · exact zero
      · exfalso
        have bounds := sourceBounds_cover names formula compiled parsed levels built index inside assignment low high found coordinate zero
        omega
    simpa [below, completions] using zero

/-- The source coordinate search and integer residual update. Empty bounds return `none`. -/
def select (levels : List (List Piece)) (index : Nat) (assignment : Nat → Int) (rank : Nat) :
    Option (Int × Int) := do
  let (low, high) ← sourceBounds
    (LatticeCumulative.cumulativePieces levels index (prefixValues assignment index))
  let coordinate := LatticeRank.search low high
    (fun bound => decide ((rank : Rat) < cumulative levels index assignment bound))
  pure (coordinate, (rank : Int) - (cumulative levels index assignment (coordinate - 1)).num)

/-- Exact rational counts give exactly the finite-table binary-search predicate. -/
theorem search_eq_table (levels : List (List Piece)) (index : Nat) (assignment : Nat → Int)
    (table : List (LatticeRank.Section Nat))
    (through : ∀ bound, (LatticeRank.through id table bound : Rat) = cumulative levels index assignment bound)
    (low high : Int) (rank : Nat) :
    LatticeRank.search low high (fun bound => decide ((rank : Rat) < cumulative levels index assignment bound)) =
      LatticeRank.selectCoordinate low high (LatticeRank.through id table) rank := by
  have predicates : (fun bound => decide ((rank : Rat) < cumulative levels index assignment bound)) =
      (fun bound => decide (rank < LatticeRank.through id table bound)) := by
    funext bound
    rw [← through bound, LatticeRank.rational_count_predicate]
  rw [predicates]
  rfl

/-- Every valid source rank selects a live coordinate and a valid residual rank. -/
theorem select_exists (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int) (rank : Nat)
    (valid : rank < naturalCount (total (levels.getD index []) assignment)) :
    ∃ coordinate : Int, ∃ residual : Nat,
      select levels index assignment rank = some (coordinate, (residual : Int)) ∧
      residual < naturalCount (completions levels index assignment coordinate) ∧
      naturalCount (cumulative levels index assignment (coordinate - 1)) + residual = rank := by
  obtain ⟨table, unique, tableTotal, through, pointwise⟩ :=
    compiled_coordinate_table names formula compiled parsed levels built index inside assignment
  have tableValid : rank < LatticeRank.sectionTotal id table := by
    rw [← tableTotal] at valid
    simpa only [naturalCount, Rat.num_natCast, Int.toNat_natCast] using valid
  have live : total (levels.getD index []) assignment ≠ 0 := by
    intro zero
    rw [zero] at valid
    simp [naturalCount] at valid
  obtain ⟨low, high, found, ordered⟩ :=
    sourceBounds_exists names formula compiled parsed levels built index inside assignment live
  have before : LatticeRank.through id table (low - 1) = 0 := by
    apply Rat.natCast_inj.mp
    rw [through]
    exact cumulative_before names formula compiled parsed levels built index inside assignment low high found
  have after : LatticeRank.through id table high = LatticeRank.sectionTotal id table := by
    apply Rat.natCast_inj.mp
    rw [through, tableTotal]
    exact cumulative_after names formula compiled parsed levels built index inside assignment low high found
  let coordinate := LatticeRank.selectCoordinate low high (LatticeRank.through id table) rank
  have chosen := LatticeRank.selected_section low high (LatticeRank.through id table) rank
    ordered before (by simpa [after] using tableValid) (LatticeRank.through_monotone id table)
  have step := LatticeRank.through_step id table coordinate
  let residual := rank - LatticeRank.through id table (coordinate - 1)
  have residualValid : residual < LatticeRank.atCoordinate id table coordinate := by
    dsimp only [residual, coordinate] at *
    omega
  have adds : LatticeRank.through id table (coordinate - 1) + residual = rank := by
    dsimp only [residual, coordinate] at *
    omega
  refine ⟨coordinate, residual, ?_, ?_, ?_⟩
  · simp only [select, found, search_eq_table levels index assignment table through]
    change some (coordinate, (rank : Int) - (cumulative levels index assignment (coordinate - 1)).num) = _
    rw [← through, LatticeRank.integer_residual rank _ (by dsimp only [coordinate] at *; omega)]
  · simpa [← pointwise coordinate, naturalCount] using residualValid
  · simpa [← through (coordinate - 1), naturalCount] using adds

/-- A coordinate and a valid child rank determine a valid parent rank. -/
theorem encode_range (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int)
    (coordinate : Int) (residual : Nat)
    (valid : residual < naturalCount (completions levels index assignment coordinate)) :
    naturalCount (cumulative levels index assignment (coordinate - 1)) + residual <
      naturalCount (total (levels.getD index []) assignment) := by
  obtain ⟨table, _, tableTotal, through, pointwise⟩ :=
    compiled_coordinate_table names formula compiled parsed levels built index inside assignment
  have childValid : residual < LatticeRank.atCoordinate id table coordinate := by
    simpa [← pointwise coordinate, naturalCount] using valid
  have step := LatticeRank.through_step id table coordinate
  have bounded := LatticeRank.through_le_total id table coordinate
  simp only [← through, ← tableTotal, naturalCount, Rat.num_natCast, Int.toNat_natCast]
  omega

/-- Polynomial binary selection inverts the source cumulative-offset rank step. -/
theorem select_encode (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (index : Nat) (inside : index < names.length) (assignment : Nat → Int)
    (coordinate : Int) (residual : Nat)
    (valid : residual < naturalCount (completions levels index assignment coordinate)) :
    select levels index assignment
      (naturalCount (cumulative levels index assignment (coordinate - 1)) + residual) =
      some (coordinate, (residual : Int)) := by
  have parentValid := encode_range names formula compiled parsed levels built index inside assignment coordinate residual valid
  obtain ⟨selected, remaining, decoded, remainingValid, adds⟩ :=
    select_exists names formula compiled parsed levels built index inside assignment _ parentValid
  obtain ⟨table, _, _, through, pointwise⟩ :=
    compiled_coordinate_table names formula compiled parsed levels built index inside assignment
  have cv : residual < LatticeRank.atCoordinate id table coordinate := by
    simpa [← pointwise coordinate, naturalCount] using valid
  have sv : remaining < LatticeRank.atCoordinate id table selected := by
    simpa [← pointwise selected, naturalCount] using remainingValid
  have equalOffsets : LatticeRank.through id table (selected - 1) + remaining =
      LatticeRank.through id table (coordinate - 1) + residual := by
    simpa [← through, naturalCount] using adds
  have cs := LatticeRank.through_step id table coordinate
  have ss := LatticeRank.through_step id table selected
  have same : selected = coordinate := LatticeRank.section_coordinate_unique
    (LatticeRank.through id table) (LatticeRank.through_monotone id table)
    (LatticeRank.through id table (coordinate - 1) + residual) selected coordinate
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  subst selected
  have restSame : remaining = residual := by omega
  simpa [restSame] using decoded

/-- The terminal stored level is exactly the original core formula indicator. -/
theorem terminal_indicator (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (assignment : Nat → Int) :
    total (levels.getD names.length []) assignment =
      if CoreFormula.evalFormula (LatticeInput.nameValues names assignment) formula then 1 else 0 := by
  rw [buildLevels_input names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) levels built,
    LatticeInput.initial_total, CoreLattice.signed_indicator (LatticeInput.variableOf names)
      (LatticeInput.nameValues names assignment) assignment (LatticeInput.nameValues_correct names assignment)
      formula compiled parsed]
  cases CoreFormula.evalFormula (LatticeInput.nameValues names assignment) formula <;> rfl

/-- Decode source ranks recursively with polynomial coordinate selection. -/
def decodeFrom (levels : List (List Piece)) : Nat → Nat → (Nat → Int) → Nat → Option (List Int)
  | 0, _, _, _ => some []
  | remaining + 1, index, assignment, rank => do
      let (coordinate, residual) ← select levels index assignment rank
      if residual < 0 then none
      else
        let rest ← decodeFrom levels remaining (index + 1)
          (LatticeBound.update assignment index coordinate) residual.toNat
        pure (coordinate :: rest)

/-- Rank a tuple by source cumulative offsets and terminal formula membership. -/
def rankFrom (levels : List (List Piece)) : Nat → Nat → (Nat → Int) → List Int → Option Nat
  | 0, index, assignment, [] => if total (levels.getD index []) assignment = 1 then some 0 else none
  | remaining + 1, index, assignment, coordinate :: rest => do
      let residual ← rankFrom levels remaining (index + 1)
        (LatticeBound.update assignment index coordinate) rest
      pure (naturalCount (cumulative levels index assignment (coordinate - 1)) + residual)
  | _, _, _, _ => none

/-- Every successfully ranked tuple has a valid rank in its actual stored completion count. -/
theorem rankFrom_range (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (remaining index : Nat) (dimension : remaining + index = names.length)
    (assignment : Nat → Int) (tuple : List Int) (rank : Nat)
    (ranked : rankFrom levels remaining index assignment tuple = some rank) :
    rank < naturalCount (total (levels.getD index []) assignment) := by
  induction remaining generalizing index assignment tuple rank with
  | zero =>
      cases tuple with
      | nil =>
          simp only [rankFrom] at ranked
          split at ranked
          · rename_i one
            cases ranked
            rw [one]
            decide
          · cases ranked
      | cons coordinate rest => simp [rankFrom] at ranked
  | succ remaining ih =>
      cases tuple with
      | nil => simp [rankFrom] at ranked
      | cons coordinate rest =>
          cases child : rankFrom levels remaining (index + 1)
              (LatticeBound.update assignment index coordinate) rest with
          | none => simp [rankFrom, child] at ranked
          | some residual =>
              have childValid := ih (index + 1) (by omega)
                (LatticeBound.update assignment index coordinate) rest residual child
              have parentValid := encode_range names formula compiled parsed levels built index
                (by omega) assignment coordinate residual childValid
              have rankEq : naturalCount (cumulative levels index assignment (coordinate - 1)) + residual = rank := by
                simpa [rankFrom, child] using ranked
              rwa [rankEq] at parentValid

/-- Every admitted tuple is recovered by polynomial decoding of its cumulative rank. -/
theorem decodeFrom_rankFrom (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (remaining index : Nat) (dimension : remaining + index = names.length)
    (assignment : Nat → Int) (tuple : List Int) (rank : Nat)
    (ranked : rankFrom levels remaining index assignment tuple = some rank) :
    decodeFrom levels remaining index assignment rank = some tuple := by
  induction remaining generalizing index assignment tuple rank with
  | zero =>
      cases tuple with
      | nil => rfl
      | cons coordinate rest => simp [rankFrom] at ranked
  | succ remaining ih =>
      cases tuple with
      | nil => simp [rankFrom] at ranked
      | cons coordinate rest =>
          cases child : rankFrom levels remaining (index + 1)
              (LatticeBound.update assignment index coordinate) rest with
          | none => simp [rankFrom, child] at ranked
          | some residual =>
              have childValid := rankFrom_range names formula compiled parsed levels built remaining (index + 1)
                (by omega) (LatticeBound.update assignment index coordinate) rest residual child
              have chosen := select_encode names formula compiled parsed levels built index
                (by omega) assignment coordinate residual childValid
              have decoded := ih (index + 1) (by omega)
                (LatticeBound.update assignment index coordinate) rest residual child
              have rankEq : naturalCount (cumulative levels index assignment (coordinate - 1)) + residual = rank := by
                simpa [rankFrom, child] using ranked
              rw [← rankEq]
              simp [decodeFrom, chosen, decoded]

/-- Every valid polynomial rank decodes and re-encodes to the original rank. -/
theorem decodeFrom_exists (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (remaining index : Nat) (dimension : remaining + index = names.length)
    (assignment : Nat → Int) (rank : Nat)
    (valid : rank < naturalCount (total (levels.getD index []) assignment)) :
    ∃ tuple, decodeFrom levels remaining index assignment rank = some tuple ∧
      rankFrom levels remaining index assignment tuple = some rank := by
  induction remaining generalizing index assignment rank with
  | zero =>
      have indexEq : index = names.length := by omega
      subst index
      have terminal := terminal_indicator names formula compiled parsed levels built assignment
      cases h : CoreFormula.evalFormula (LatticeInput.nameValues names assignment) formula
      · simp only [h, Bool.false_eq_true, ↓reduceIte] at terminal
        rw [terminal] at valid
        simp [naturalCount] at valid
      · simp only [h, ↓reduceIte] at terminal
        rw [terminal] at valid
        have zero : rank = 0 := by simpa [naturalCount] using valid
        subst rank
        refine ⟨[], rfl, ?_⟩
        simp only [rankFrom, terminal, ↓reduceIte]
  | succ remaining ih =>
      obtain ⟨coordinate, residual, chosen, childValid, adds⟩ :=
        select_exists names formula compiled parsed levels built index (by omega) assignment rank valid
      obtain ⟨rest, decoded, ranked⟩ := ih (index + 1) (by omega)
        (LatticeBound.update assignment index coordinate) residual childValid
      refine ⟨coordinate :: rest, ?_, ?_⟩
      · simp [decodeFrom, chosen, decoded]
      · simp [rankFrom, ranked, adds]

/-- Assign the tuple coordinates in the same order as the source prefix map. -/
def assignTuple (assignment : Nat → Int) (index : Nat) : List Int → (Nat → Int)
  | [] => assignment
  | coordinate :: rest => assignTuple (LatticeBound.update assignment index coordinate) (index + 1) rest

/-- Ranking is defined exactly for tuples of the required length whose terminal indicator is one. -/
theorem rankFrom_membership (levels : List (List Piece)) (remaining index : Nat)
    (assignment : Nat → Int) (tuple : List Int) :
    (∃ rank, rankFrom levels remaining index assignment tuple = some rank) ↔
      tuple.length = remaining ∧
        total (levels.getD (index + tuple.length) []) (assignTuple assignment index tuple) = 1 := by
  induction remaining generalizing index assignment tuple with
  | zero =>
      cases tuple with
      | nil =>
          by_cases accepted : total (levels.getD index []) assignment = 1 <;>
            simp only [rankFrom, accepted, ↓reduceIte, List.length_nil, Nat.add_zero, assignTuple] <;>
            simp
      | cons coordinate rest => simp [rankFrom]
  | succ remaining ih =>
      cases tuple with
      | nil => simp [rankFrom]
      | cons coordinate rest =>
          have recursive :=  ih (index + 1) (LatticeBound.update assignment index coordinate) rest
          constructor
          · rintro ⟨rank, ranked⟩
            cases child : rankFrom levels remaining (index + 1)
                (LatticeBound.update assignment index coordinate) rest with
            | none => simp [rankFrom, child] at ranked
            | some residual =>
                have admitted := recursive.mp ⟨residual, child⟩
                refine ⟨by simp [admitted.1], ?_⟩
                simpa [assignTuple, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using admitted.2
          · rintro ⟨length, admitted⟩
            have childLength : rest.length = remaining := by simpa using length
            have childAdmitted : total (levels.getD (index + 1 + rest.length) [])
                (assignTuple (LatticeBound.update assignment index coordinate) (index + 1) rest) = 1 := by
              simpa [assignTuple, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using admitted
            obtain ⟨residual, ranked⟩ := recursive.mpr ⟨childLength, childAdmitted⟩
            exact ⟨naturalCount (cumulative levels index assignment (coordinate - 1)) + residual,
              by simp [rankFrom, ranked]⟩

/-- The source's stored constant count equals the semantic count at the empty prefix. -/
theorem root_count (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (assignment : Nat → Int) :
    polynomialCount (levels.getD 0 []) = total (levels.getD 0 []) assignment := by
  exact polynomialCount_correct assignment (List.range names.length).reverse
    (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled)
    (LatticeInput.initial_metadata compiled)
    (LatticeInput.initial_covers names (CoreLattice.lowerFormula formula) compiled parsed)
    (levels.getD 0 [])
    (LatticeAPI.buildLevels_sumOut names.length (LatticeInput.initial compiled)
      (LatticeInput.initial_valid compiled) levels built)

/-- The source count as a natural number. Integrality follows from formula compilation. -/
def pointCount (levels : List (List Piece)) : Nat := naturalCount (polynomialCount (levels.getD 0 []))

/-- The actual source polynomial decoder on its finite rank domain. -/
def decode (dimension : Nat) (levels : List (List Piece)) (rank : Fin (pointCount levels)) : List Int :=
  (decodeFrom levels dimension 0 (fun _ => 0) rank.val).getD []

/-- The independent predicate for an integer tuple satisfying the source formula. -/
def Admits (names : List CoreFormula.Name) (formula : CoreFormula.Formula) (tuple : List Int) : Prop :=
  tuple.length = names.length ∧
    CoreFormula.evalFormula (LatticeInput.nameValues names (assignTuple (fun _ => 0) 0 tuple)) formula = true

/-- The source cumulative rank is defined exactly on the independent formula solution set. -/
theorem ranked_iff_admits (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (tuple : List Int) :
    (∃ rank, rankFrom levels names.length 0 (fun _ => 0) tuple = some rank) ↔ Admits names formula tuple := by
  rw [rankFrom_membership]
  unfold Admits
  constructor
  · rintro ⟨length, accepted⟩
    refine ⟨length, ?_⟩
    simp only [Nat.zero_add, length] at accepted
    rw [terminal_indicator names formula compiled parsed levels built] at accepted
    cases h : CoreFormula.evalFormula
      (LatticeInput.nameValues names (assignTuple (fun _ => 0) 0 tuple)) formula <;>
      simp_all
  · rintro ⟨length, accepted⟩
    refine ⟨length, ?_⟩
    simp only [Nat.zero_add, length]
    rw [terminal_indicator names formula compiled parsed levels built]
    simp [accepted]

/-- A finite source rank always has an actual polynomial decoding. -/
theorem decode_defined (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (rank : Fin (pointCount levels)) :
    decodeFrom levels names.length 0 (fun _ => 0) rank.val = some (decode names.length levels rank) ∧
      rankFrom levels names.length 0 (fun _ => 0) (decode names.length levels rank) = some rank.val := by
  have valid : rank.val < naturalCount (total (levels.getD 0 []) (fun _ => 0)) := by
    rw [← root_count names formula compiled parsed levels built]
    exact rank.isLt
  obtain ⟨tuple, decoded, ranked⟩ := decodeFrom_exists names formula compiled parsed levels built
    names.length 0 (by omega) (fun _ => 0) rank.val valid
  simpa [decode, decoded] using And.intro decoded ranked

/-- Polynomial decoding produces only correctly sized tuples satisfying the core formula. -/
theorem decode_admits (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (rank : Fin (pointCount levels)) : Admits names formula (decode names.length levels rank) := by
  exact (ranked_iff_admits names formula compiled parsed levels built _).mp
    ⟨rank.val, (decode_defined names formula compiled parsed levels built rank).2⟩

/-- Every tuple satisfying the formula has a source rank below the actual stored count. -/
theorem decode_surjective (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (tuple : List Int) (admitted : Admits names formula tuple) :
    ∃ rank : Fin (pointCount levels), decode names.length levels rank = tuple := by
  obtain ⟨rank, ranked⟩ := (ranked_iff_admits names formula compiled parsed levels built tuple).mpr admitted
  have valid := rankFrom_range names formula compiled parsed levels built names.length 0 (by omega)
    (fun _ => 0) tuple rank ranked
  have countValid : rank < pointCount levels := by
    unfold pointCount
    rwa [root_count names formula compiled parsed levels built]
  have decoded := decodeFrom_rankFrom names formula compiled parsed levels built names.length 0
    (by omega) (fun _ => 0) tuple rank ranked
  exact ⟨⟨rank, countValid⟩, by simp [decode, decoded]⟩

/-- Distinct source ranks decode to distinct satisfying tuples. -/
theorem decode_injective (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels) :
    Function.Injective (decode names.length levels) := by
  intro left right same
  have first := (decode_defined names formula compiled parsed levels built left).2
  have second := (decode_defined names formula compiled parsed levels built right).2
  rw [same] at first
  apply Fin.ext
  exact Option.some.inj (first.symm.trans second)

/-- The actual compiled polynomial decoder is a bijection from `0..n-1` to all valid tuples. -/
theorem points_exact (names : List CoreFormula.Name) (formula : CoreFormula.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : CoreLattice.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels) :
    (∀ tuple, Admits names formula tuple ↔
      ∃ rank : Fin (pointCount levels), decode names.length levels rank = tuple) ∧
      Function.Injective (decode names.length levels) := by
  refine ⟨?_, decode_injective names formula compiled parsed levels built⟩
  intro tuple
  constructor
  · exact decode_surjective names formula compiled parsed levels built tuple
  · rintro ⟨rank, rfl⟩
    exact decode_admits names formula compiled parsed levels built rank

/-- The same actual decoder theorem covers every successful parse of the current full formula syntax. -/
theorem fullSyntax_points_exact (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : FullSyntax.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels) :
    (∀ tuple, (tuple.length = names.length ∧ FullSyntax.Holds FullSyntax.integerModel
        (LatticeInput.nameValues names (assignTuple (fun _ => 0) 0 tuple)) formula) ↔
      ∃ rank : Fin (pointCount levels), decode names.length levels rank = tuple) ∧
      Function.Injective (decode names.length levels) := by
  obtain ⟨core, equal, coreParsed⟩ := FullSyntax.signed_success_is_core _ true formula compiled parsed
  rw [← equal]
  simpa only [FullSyntax.embedFormula_holds, Admits] using
    points_exact names core compiled coreParsed levels built

/-- The public source constructor's stored integer count and decoder satisfy the finite-rank specification. -/
theorem points_api_exact (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (result : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok result) :
    result.count.toNat = pointCount result.levels ∧ result.dimension = names.length ∧
    (∀ tuple, (tuple.length = names.length ∧ FullSyntax.Holds FullSyntax.integerModel
        (LatticeInput.nameValues names (assignTuple (fun _ => 0) 0 tuple)) formula) ↔
      ∃ rank : Fin (pointCount result.levels), decode result.dimension result.levels rank = tuple) ∧
      Function.Injective (decode result.dimension result.levels) := by
  obtain ⟨compiled, parsed, built, dimension, countEq⟩ :=
    LatticeAPI.points_success names (FullSyntax.lowerFormula formula) result success
  refine ⟨?_, dimension, ?_⟩
  · simp only [countEq, pointCount, naturalCount]
  · rw [dimension]
    exact fullSyntax_points_exact names formula compiled parsed result.levels built

/-- Count conversion preserves the exact numerator used by the source rank sum. -/
theorem naturalCount_numerator (value : Rat) (natural : ∃ count : Nat, value = (count : Rat)) :
    (naturalCount value : Int) = value.num := by
  obtain ⟨count, rfl⟩ := natural
  simp [naturalCount]

/-- One source coordinate search needs at most `bits` cumulative polynomial queries. -/
theorem select_query_bound (levels : List (List Piece)) (index : Nat) (assignment : Nat → Int)
    (rank bits : Nat) (low high : Int)
    (width : (high - low).toNat < 2 ^ bits) :
    (SearchCost.measured low high
      (fun bound => decide ((rank : Rat) < cumulative levels index assignment bound))).2 ≤ bits := by
  exact SearchCost.logarithmic_queries bits low high _ width

/-- Supply point closure with the actual polynomial decoder. -/
def compiledPoints (dimension : Nat) (levels : List (List Piece)) : ZeroSize.Points dimension where
  count := pointCount levels
  decode rank := LatticeRank.tupleFunction dimension (decode dimension levels rank)

/-- The actual public point constructor discharges the exact-points obligation used by generator closure. -/
theorem compiledPoints_exact (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : FullSyntax.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels) :
    ZeroSize.ExactPoints (compiledPoints names.length levels)
      (fun tuple => FullSyntax.Holds FullSyntax.integerModel
        (LatticeInput.nameValues names (assignTuple (fun _ => 0) 0 (List.ofFn tuple))) formula) := by
  have exactness := fullSyntax_points_exact names formula compiled parsed levels built
  have decodedAdmits : ∀ rank : Fin (pointCount levels),
      (decode names.length levels rank).length = names.length ∧
      FullSyntax.Holds FullSyntax.integerModel
        (LatticeInput.nameValues names (assignTuple (fun _ => 0) 0 (decode names.length levels rank))) formula := by
    intro rank
    exact (exactness.1 _).mpr ⟨rank, rfl⟩
  constructor
  · intro tuple
    constructor
    · intro admitted
      obtain ⟨rank, decoded⟩ := (exactness.1 (List.ofFn tuple)).mp ⟨by simp, admitted⟩
      refine ⟨rank, ?_⟩
      change LatticeRank.tupleFunction names.length (decode names.length levels rank) = tuple
      rw [decoded, LatticeRank.tupleFunction_ofFn]
    · rintro ⟨rank, decoded⟩
      change LatticeRank.tupleFunction names.length (decode names.length levels rank) = tuple at decoded
      rw [← decoded, LatticeRank.ofFn_tupleFunction _ _ (decodedAdmits rank).1]
      exact (decodedAdmits rank).2
  · intro left right same
    apply exactness.2
    have lists := congrArg List.ofFn same
    change List.ofFn (LatticeRank.tupleFunction names.length (decode names.length levels left)) =
      List.ofFn (LatticeRank.tupleFunction names.length (decode names.length levels right)) at lists
    simpa only [LatticeRank.ofFn_tupleFunction _ _ (decodedAdmits left).1,
      LatticeRank.ofFn_tupleFunction _ _ (decodedAdmits right).1] using lists

/-- Closing generator outcomes over actual compiled points neither drops nor introduces solutions. -/
theorem closePoints_exact {Value : Type} (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : FullSyntax.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List Piece))
    (built : buildLevels names.length (LatticeInput.initial compiled) (LatticeInput.initial_valid compiled) = .ok levels)
    (sources : List (ZeroSize.OpenOutcome names.length Value)) (size : Nat) (value : Value) :
    (size, value) ∈ ZeroSize.closePoints (compiledPoints names.length levels) sources ↔
      ∃ source, source ∈ sources ∧ ∃ tuple,
        FullSyntax.Holds FullSyntax.integerModel
          (LatticeInput.nameValues names (assignTuple (fun _ => 0) 0 (List.ofFn tuple))) formula ∧
        size = source.1 + names.length ∧ value = source.2 tuple := by
  exact ZeroSize.closePoints_exact (compiledPoints names.length levels) _
    (compiledPoints_exact names formula compiled parsed levels built) sources size value

end MicroCFTA.LatticeSelect
