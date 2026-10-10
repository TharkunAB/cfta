import MicroCFTA.LatticeCount
import MicroCFTA.LatticeInterval

/-!
# Stored counting levels

The caller eliminates variables from the last index to zero. It retains every
intermediate piece list. Level `k` contains the completion counts after all
variables with index at least `k` have been summed out.
-/

namespace MicroCFTA.LatticeLevels

open LatticeLinear LatticePiece LatticePipeline LatticeCount

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- Construct the source's retained levels, from the fully summed level to the input. -/
def buildLevels : (dimension : Nat) → (pieces : List Piece) →
    (∀ piece ∈ pieces, ValidPiece piece) → Except SplitError (List (List Piece))
  | 0, pieces, _ => .ok [pieces]
  | dimension + 1, pieces, valid =>
    match next : eliminate dimension pieces valid with
    | .error error => .error error
    | .ok output =>
      match buildLevels dimension output (eliminate_valid dimension pieces valid output next) with
      | .error error => .error error
      | .ok levels => .ok (levels ++ [pieces])

/-- Lookup before the append boundary sees only the original list. -/
theorem getD_append_left (left right : List α) (fallback : α) (index : Nat) (before : index < left.length) :
    (left ++ right).getD index fallback = left.getD index fallback := by
  induction left generalizing index with
  | nil => simp at before
  | cons item rest ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih index (by simpa using before)

/-- Appending one item places it precisely at the original length. -/
theorem getD_append_last (items : List α) (item fallback : α) :
    (items ++ [item]).getD items.length fallback = item := by
  induction items with
  | nil => rfl
  | cons head rest ih => exact ih

/-- The retained table has one level for every prefix dimension, including zero. -/
theorem buildLevels_length (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels) :
    levels.length = dimension + 1 := by
  induction dimension generalizing pieces levels with
  | zero => simp [buildLevels] at success; cases success; rfl
  | succ dimension ih =>
    unfold buildLevels at success
    split at success
    · cases success
    · next nextPieces found =>
      split at success
      · cases success
      · next previous built =>
        cases success
        simp [List.length_append, ih nextPieces _ previous built]

/-- The last level is the source input, before any variable is removed. -/
theorem buildLevels_input (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels) :
    levels.getD dimension [] = pieces := by
  cases dimension with
  | zero => simp [buildLevels] at success; cases success; rfl
  | succ dimension =>
    unfold buildLevels at success
    split at success
    · cases success
    · next nextPieces found =>
      split at success
      · cases success
      · next previous built =>
        cases success
        have length := buildLevels_length dimension nextPieces _ previous built
        rw [← length, getD_append_last]

/-- Every retained level is valid input to the same source algorithms. -/
theorem buildLevels_valid (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels) :
    ∀ level ∈ levels, ∀ piece ∈ level, ValidPiece piece := by
  induction dimension generalizing pieces levels with
  | zero =>
    simp [buildLevels] at success
    cases success
    intro level member
    obtain rfl := List.mem_singleton.mp member
    exact valid
  | succ dimension ih =>
    unfold buildLevels at success
    split at success
    · cases success
    · next nextPieces found =>
      split at success
      · cases success
      · next previous built =>
        cases success
        intro level member
        rcases List.mem_append.mp member with earlier | original
        · exact ih nextPieces _ previous built level earlier
        · obtain rfl := List.mem_singleton.mp original
          exact valid

/-- One genuine successful source elimination connects two adjacent levels. -/
def Step (index : Nat) (input output : List Piece) : Prop :=
  ∃ valid : ∀ piece ∈ input, ValidPiece piece, eliminate index input valid = .ok output

/-- Every adjacent stored pair comes from the correct variable's elimination. -/
theorem buildLevels_step (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) :
    Step index (levels.getD (index + 1) []) (levels.getD index []) := by
  induction dimension generalizing pieces levels with
  | zero => omega
  | succ dimension ih =>
    unfold buildLevels at success
    split at success
    · cases success
    · next nextPieces found =>
      split at success
      · cases success
      · next previous built =>
        cases success
        have length := buildLevels_length dimension nextPieces _ previous built
        by_cases last : index = dimension
        · subst index
          rw [← length, getD_append_last, getD_append_left _ _ _ dimension (by omega),
            buildLevels_input dimension nextPieces _ previous built]
          exact ⟨valid, found⟩
        · rw [getD_append_left _ _ _ (index + 1) (by omega), getD_append_left _ _ _ index (by omega)]
          exact ih nextPieces _ previous built (by omega)

/-- Each level is the exact integer sum of the next level at the current variable. -/
theorem buildLevels_sum (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) (assignment : Nat → Int) :
    FiniteSum.HasSum (fun value => total (levels.getD (index + 1) []) (LatticeBound.update assignment index value))
      (total (levels.getD index []) assignment) := by
  obtain ⟨canonical, found⟩ := buildLevels_step dimension pieces valid levels success index inside
  exact eliminate_sum assignment index _ canonical _ found

/-- Every level above the current prefix has no remaining dependence on later variables. -/
theorem buildLevels_free (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (outside : ∀ index, dimension ≤ index → ∀ piece ∈ pieces, FreePiece index piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (level : Nat) (levelBound : level ≤ dimension) :
    ∀ index, level ≤ index → ∀ piece ∈ levels.getD level [], FreePiece index piece := by
  induction dimension generalizing pieces levels level with
  | zero =>
    have zeroLevel : level = 0 := by omega
    subst level
    rw [buildLevels_input 0 pieces valid levels success]
    exact outside
  | succ dimension ih =>
    unfold buildLevels at success
    split at success
    · cases success
    · next nextPieces found =>
      split at success
      · cases success
      · next previous built =>
        cases success
        have length := buildLevels_length dimension nextPieces _ previous built
        by_cases last : level = dimension + 1
        · subst level
          rw [← length, getD_append_last]
          simpa only [length] using outside
        · rw [getD_append_left _ _ _ level (by omega)]
          apply ih nextPieces _ _ previous built level (by omega)
          intro index later
          by_cases same : index = dimension
          · subst index
            exact eliminate_removes dimension pieces valid nextPieces found
          · exact eliminate_preserves_free index dimension pieces valid (outside index (by omega)) nextPieces found

/-- Every stored completion value is a natural number if the input is indicator-valued. -/
theorem buildLevels_natural (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (natural : ∀ assignment, ∃ n : Nat, total pieces assignment = (n : Rat))
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (level : Nat) (levelBound : level ≤ dimension) :
    ∀ assignment, ∃ n : Nat, total (levels.getD level []) assignment = (n : Rat) := by
  induction dimension generalizing pieces levels level with
  | zero =>
    have zeroLevel : level = 0 := by omega
    subst level
    rw [buildLevels_input 0 pieces valid levels success]
    exact natural
  | succ dimension ih =>
    unfold buildLevels at success
    split at success
    · cases success
    · next nextPieces found =>
      split at success
      · cases success
      · next previous built =>
        cases success
        have length := buildLevels_length dimension nextPieces _ previous built
        by_cases last : level = dimension + 1
        · subst level
          rw [← length, getD_append_last]
          exact natural
        · rw [getD_append_left _ _ _ level (by omega)]
          apply ih nextPieces _ _ previous built level (by omega)
          intro assignment
          exact FiniteSum.natural (eliminate_sum assignment dimension pieces valid nextPieces found)
            (fun value => natural (LatticeBound.update assignment dimension value))

/-- A returned lower bound can only come from coefficient one. -/
theorem bound_lower_coefficient (index : Nat) (linear lower : Linear)
    (success : LatticeBound.bound index linear = .ok (.inl lower)) : LatticeBound.coefficientOf index linear = 1 := by
  unfold LatticeBound.bound at success
  split at success
  · assumption
  · split at success <;> cases success

/-- A returned upper bound can only come from coefficient minus one. -/
theorem bound_upper_coefficient (index : Nat) (linear upper : Linear)
    (success : LatticeBound.bound index linear = .ok (.inr upper)) : LatticeBound.coefficientOf index linear = -1 := by
  unfold LatticeBound.bound at success
  split at success
  · cases success
  · split at success
    · assumption
    · cases success

/-- A nonempty collected lower list supplies an actual lower inequality in the input. -/
theorem collected_lower (index : Nat) (forms lowers uppers : List Linear)
    (success : collectBounds index forms = .ok (lowers, uppers)) (nonempty : 0 < lowers.length) :
    ∃ form ∈ forms, LatticeBound.coefficientOf index form = 1 := by
  induction forms generalizing lowers uppers with
  | nil =>
    simp only [collectBounds] at success
    cases success
    simp at nonempty
  | cons form rest ih =>
    cases first : LatticeBound.bound index form with
    | error error => simp [collectBounds, first] at success
    | ok firstBound =>
      cases tail : collectBounds index rest with
      | error error => simp [collectBounds, first, tail] at success
      | ok bounds =>
        rcases bounds with ⟨ls, us⟩
        cases firstBound with
        | inl lower => exact ⟨form, by simp, bound_lower_coefficient index form lower first⟩
        | inr upper =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          obtain ⟨original, member, coefficient⟩ := ih ls us tail nonempty
          exact ⟨original, by simp [member], coefficient⟩

/-- A nonempty collected upper list supplies an actual upper inequality in the input. -/
theorem collected_upper (index : Nat) (forms lowers uppers : List Linear)
    (success : collectBounds index forms = .ok (lowers, uppers)) (nonempty : 0 < uppers.length) :
    ∃ form ∈ forms, LatticeBound.coefficientOf index form = -1 := by
  induction forms generalizing lowers uppers with
  | nil =>
    simp only [collectBounds] at success
    cases success
    simp at nonempty
  | cons form rest ih =>
    cases first : LatticeBound.bound index form with
    | error error => simp [collectBounds, first] at success
    | ok firstBound =>
      cases tail : collectBounds index rest with
      | error error => simp [collectBounds, first, tail] at success
      | ok bounds =>
        rcases bounds with ⟨ls, us⟩
        cases firstBound with
        | inl lower =>
          simp [collectBounds, first, tail] at success
          rcases success with ⟨rfl, rfl⟩
          obtain ⟨original, member, coefficient⟩ := ih ls us tail nonempty
          exact ⟨original, by simp [member], coefficient⟩
        | inr upper => exact ⟨form, by simp, bound_upper_coefficient index form upper first⟩

/-- Successful source splitting proves that both original bound directions exist. -/
theorem splitFull_bounded (index : Nat) (piece : Piece) (valid : ValidPiece piece)
    (output : List Piece) (success : splitFull index piece valid = .ok output) :
    (∃ form ∈ piece.constraints, 0 < LatticeBound.coefficientOf index form) ∧
    (∃ form ∈ piece.constraints, LatticeBound.coefficientOf index form < 0) := by
  obtain ⟨raw, found, _⟩ := splitFull_success index piece valid output success
  obtain ⟨lowers, uppers, collected, hl, hu, _⟩ := splitRaw_success index piece raw found
  obtain ⟨lower, lowerMember, lowerCoefficient⟩ := collected_lower index _ lowers uppers collected hl
  obtain ⟨upper, upperMember, upperCoefficient⟩ := collected_upper index _ lowers uppers collected hu
  exact ⟨⟨lower, (List.mem_filter.mp lowerMember).1, by omega⟩,
    ⟨upper, (List.mem_filter.mp upperMember).1, by omega⟩⟩

/-- Success of list traversal establishes the complete split of every source member. -/
theorem eliminate_each (index : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (output : List Piece) (success : eliminate index pieces valid = .ok output) :
    ∀ piece ∈ pieces, ∃ canonical : ValidPiece piece, ∃ result, splitFull index piece canonical = .ok result := by
  induction pieces generalizing output with
  | nil => simp
  | cons piece rest ih =>
    cases first : splitFull index piece (valid piece (by simp)) with
    | error error => simp [eliminate, first] at success
    | ok head =>
      cases tail : eliminate index rest (fun item member => valid item (by simp [member])) with
      | error error => simp [eliminate, first, tail] at success
      | ok remaining =>
        intro item member
        rcases List.mem_cons.mp member with same | member
        · subst item; exact ⟨valid piece (by simp), head, first⟩
        · exact ih _ remaining tail item member

/-- Every piece decoded at a level has both required bound directions from its actual successful compilation. -/
theorem buildLevels_bounded (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) :
    ∀ piece ∈ levels.getD (index + 1) [],
      (∃ form ∈ piece.constraints, 0 < LatticeBound.coefficientOf index form) ∧
      (∃ form ∈ piece.constraints, LatticeBound.coefficientOf index form < 0) := by
  obtain ⟨canonical, found⟩ := buildLevels_step dimension pieces valid levels success index inside
  intro piece member
  obtain ⟨pieceCanonical, output, compiled⟩ := eliminate_each index _ canonical _ found piece member
  exact splitFull_bounded index piece pieceCanonical output compiled

/-- The prefix map assigns exactly the earlier variables. -/
def prefixValues (assignment : Nat → Int) (index : Nat) : Nat → Option Int :=
  fun other => if other < index then some (assignment other) else none

@[simp] theorem prefixValues_current (assignment : Nat → Int) (index : Nat) : prefixValues assignment index index = none := by
  simp [prefixValues]

/-- Stored-level support proves the premise required by prefix interval extraction. -/
theorem buildLevels_prefix_covers (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (outside : ∀ index, dimension ≤ index → ∀ piece ∈ pieces, FreePiece index piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) (assignment : Nat → Int) :
    ∀ piece ∈ levels.getD (index + 1) [], ∀ form ∈ piece.constraints,
      LatticeInterval.PrefixCovers index (prefixValues assignment index) form := by
  intro piece member form formMember entry entryMember
  by_cases current : entry.1 = index
  · exact Or.inl current
  · have earlier : entry.1 < index := by
      by_cases before : entry.1 < index
      · exact before
      · have free := (buildLevels_free dimension pieces valid outside levels success (index + 1) (by omega)
          entry.1 (Nat.lt_of_le_of_ne (Nat.le_of_not_gt before) (Ne.symm current)) piece member).1 form formMember entry entryMember
        exact False.elim (free rfl)
    exact Or.inr ⟨assignment entry.1, by simp [prefixValues, earlier]⟩

/-- Every defaulted level lookup has valid piece metadata. -/
theorem buildLevels_lookup_valid (dimension : Nat) (pieces : List Piece) (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels) (index : Nat) :
    ∀ piece ∈ levels.getD index [], ValidPiece piece :=
  getD_property levels [] (fun level => ∀ piece ∈ level, ValidPiece piece) (by simp)
    (buildLevels_valid dimension pieces valid levels success) index

/-- Reapplying the earlier assignments leaves the current-variable update unchanged. -/
theorem prefix_update (assignment : Nat → Int) (index : Nat) (value : Int) :
    override (prefixValues assignment index) (LatticeBound.update assignment index value) =
      LatticeBound.update assignment index value := by
  funext other
  by_cases earlier : other < index
  · have apart : other ≠ index := by omega
    simp [override, prefixValues, LatticeBound.update, earlier, apart]
  · simp [override, prefixValues, earlier]

/-- Actual stored levels discharge every premise of successful prefix interval extraction. -/
theorem buildLevels_interval_correct (dimension : Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (outside : ∀ index, dimension ≤ index → ∀ piece ∈ pieces, FreePiece index piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) (assignment : Nat → Int)
    (piece : Piece) (member : piece ∈ levels.getD (index + 1) [])
    (low high : Int) (found : LatticeInterval.intervalWithPrefix index (prefixValues assignment index) piece.constraints = some (low, high)) :
    ∀ value, holds (LatticeBound.update assignment index value) piece.constraints = true ↔ low ≤ value ∧ value ≤ high := by
  intro value
  have converted := LatticeInterval.intervalWithPrefix_correct assignment index (prefixValues assignment index)
    piece.constraints (buildLevels_lookup_valid dimension pieces valid levels success (index + 1) piece member).1
    (buildLevels_prefix_covers dimension pieces valid outside levels success index inside assignment piece member)
    low high value found
  rw [prefix_update] at converted
  simpa only [holds, List.all_eq_true, decide_eq_true_eq] using converted

/-- An omitted cumulative piece has zero support under the selected prefix. -/
theorem buildLevels_interval_none (dimension : Nat) (pieces : List Piece)
    (valid : ∀ piece ∈ pieces, ValidPiece piece)
    (outside : ∀ index, dimension ≤ index → ∀ piece ∈ pieces, FreePiece index piece)
    (levels : List (List Piece)) (success : buildLevels dimension pieces valid = .ok levels)
    (index : Nat) (inside : index < dimension) (assignment : Nat → Int)
    (piece : Piece) (member : piece ∈ levels.getD (index + 1) [])
    (failure : LatticeInterval.intervalWithPrefix index (prefixValues assignment index) piece.constraints = none) :
    ∀ value, pieceValue (LatticeBound.update assignment index value) piece = 0 := by
  have bounds := buildLevels_bounded dimension pieces valid levels success index inside piece member
  have absent := LatticeInterval.intervalWithPrefix_none assignment index (prefixValues assignment index)
    (prefixValues_current assignment index) piece.constraints
    (buildLevels_lookup_valid dimension pieces valid levels success (index + 1) piece member).1
    (buildLevels_prefix_covers dimension pieces valid outside levels success index inside assignment piece member)
    bounds.1 bounds.2 failure
  intro value
  have noPoint : holds (LatticeBound.update assignment index value) piece.constraints ≠ true := by
    intro admitted
    apply absent value
    rw [prefix_update]
    intro form formMember
    exact of_decide_eq_true (List.all_eq_true.mp admitted form formMember)
  simp [pieceValue, noPoint]

end MicroCFTA.LatticeLevels
