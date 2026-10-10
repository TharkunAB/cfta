import MicroCFTA.ZeroSize

/-!
# Lexicographic integer-point ranking

`search` uses the midpoint and strict cumulative-count predicate of
`Refinement.Lattice.search` and `pointAt`. Finite sections below provide
concrete completion counts. The polynomial construction of those counts is
outside this module.

The reference sections have unique coordinate keys. They need not be sorted.
Their finite bounds include zero and enclose the support. Haskell obtains its
bounds from polyhedral pieces instead. The search theorem permits any valid
enclosure; `selectCoordinate_bounds_independent` proves agreement between
enclosures. No translation of the Haskell maps or polynomial levels is proved.
The optional rank operations add explicit range and membership checks.
-/

namespace MicroCFTA.LatticeRank

/-- The midpoint used by the integer binary search. -/
def midpoint (low high : Int) : Int := low + (high - low) / 2

/-- A nontrivial integer interval has its midpoint inside its left half. -/
theorem midpoint_bounds (low high : Int) (h : low < high) :
    low ≤ midpoint low high ∧ midpoint low high < high := by
  unfold midpoint
  omega

/-- Search the first true position in an inclusive integer interval. -/
def search (low high : Int) (predicate : Int → Bool) : Int :=
  if low ≥ high then low
  else
    let middle := midpoint low high
    if predicate middle then search low middle predicate
    else search (middle + 1) high predicate
termination_by (high - low).toNat
decreasing_by
  all_goals
    have hm := midpoint_bounds low high (by omega)
    omega

/-- A true monotone predicate stays true at larger integer arguments. -/
def MonotonePredicate (predicate : Int → Bool) : Prop :=
  ∀ low high, low ≤ high → predicate low = true → predicate high = true

/-- Binary search returns the least true point of its initial interval. -/
theorem search_correct (low high : Int) (predicate : Int → Bool)
    (bounds : low ≤ high) (upper : predicate high = true)
    (monotone : MonotonePredicate predicate) :
    low ≤ search low high predicate ∧ search low high predicate ≤ high ∧
      predicate (search low high predicate) = true ∧
      ∀ value, low ≤ value → value < search low high predicate → predicate value = false := by
  rw [search]
  split
  · next done =>
      have same : low = high := by omega
      subst high
      exact ⟨Int.le_refl _, Int.le_refl _, upper, by intro value hl hv; omega⟩
  · next more =>
      have hm := midpoint_bounds low high (by omega)
      dsimp only
      split
      · next yes =>
          have ih := search_correct low (midpoint low high) predicate hm.1 yes monotone
          exact ⟨ih.1, by omega, ih.2.2.1, ih.2.2.2⟩
      · next no =>
          have ih := search_correct (midpoint low high + 1) high predicate (by omega) upper monotone
          refine ⟨by omega, ih.2.1, ih.2.2.1, ?_⟩
          intro value hl hv
          by_cases before : value ≤ midpoint low high
          · cases hp : predicate value with
            | false => rfl
            | true => exact False.elim (no (monotone value _ before hp))
          · exact ih.2.2.2 value (by omega) hv
termination_by (high - low).toNat
decreasing_by
  all_goals
    have _hm := midpoint_bounds low high (by omega)
    omega

/-- Completion counts do not decrease as the upper coordinate bound increases. -/
def MonotoneCount (cumulative : Int → Nat) : Prop :=
  ∀ low high, low ≤ high → cumulative low ≤ cumulative high

/-- Select the first coordinate whose cumulative count exceeds the rank. -/
def selectCoordinate (low high : Int) (cumulative : Int → Nat) (rank : Nat) : Int :=
  search low high (fun value => decide (rank < cumulative value))

/-- The selected entry contains the rank, including across gaps in the support. -/
theorem selected_section (low high : Int) (cumulative : Int → Nat) (rank : Nat)
    (bounds : low ≤ high) (before : cumulative (low - 1) = 0)
    (upper : rank < cumulative high) (monotone : MonotoneCount cumulative) :
    let value := selectCoordinate low high cumulative rank
    low ≤ value ∧ value ≤ high ∧ cumulative (value - 1) ≤ rank ∧ rank < cumulative value := by
  have h := search_correct low high (fun value => decide (rank < cumulative value)) bounds
    (by simpa using upper) (by
      intro left right hl hp
      have hm := monotone left right hl
      simp only [decide_eq_true_eq] at hp ⊢
      omega)
  change low ≤ selectCoordinate low high cumulative rank ∧
    selectCoordinate low high cumulative rank ≤ high ∧
    decide (rank < cumulative (selectCoordinate low high cumulative rank)) = true ∧
    (∀ value, low ≤ value → value < selectCoordinate low high cumulative rank →
      decide (rank < cumulative value) = false) at h
  change low ≤ selectCoordinate low high cumulative rank ∧ _
  refine ⟨h.1, h.2.1, ?_, of_decide_eq_true h.2.2.1⟩
  by_cases same : selectCoordinate low high cumulative rank = low
  · simp [same, before]
  · have hm := h.2.2.2 (selectCoordinate low high cumulative rank - 1) (by omega) (by omega)
    simp only [decide_eq_false_iff_not] at hm
    omega

/-- Subtracting the count of earlier sections gives an in-range residual rank. -/
theorem residual_rank_range (low high : Int) (cumulative : Int → Nat) (rank : Nat)
    (bounds : low ≤ high) (before : cumulative (low - 1) = 0)
    (upper : rank < cumulative high) (monotone : MonotoneCount cumulative) :
    let value := selectCoordinate low high cumulative rank
    let residual := rank - cumulative (value - 1)
    residual < cumulative value - cumulative (value - 1) ∧
      cumulative (value - 1) + residual = rank := by
  have hs := selected_section low high cumulative rank bounds before upper monotone
  dsimp only at hs ⊢
  omega

/-- Two coordinates cannot contain the same rank in their cumulative intervals. -/
theorem section_coordinate_unique (cumulative : Int → Nat) (monotone : MonotoneCount cumulative)
    (rank : Nat) (left right : Int)
    (hl : cumulative (left - 1) ≤ rank ∧ rank < cumulative left)
    (hr : cumulative (right - 1) ≤ rank ∧ rank < cumulative right) : left = right := by
  by_cases hlt : left < right
  · have hm := monotone left (right - 1) (by omega)
    omega
  · by_cases hgt : right < left
    · have hm := monotone right (left - 1) (by omega)
      omega
    · omega

/-- Any two valid support enclosures select the same coordinate. -/
theorem selectCoordinate_bounds_independent
    (firstLow firstHigh secondLow secondHigh : Int) (cumulative : Int → Nat) (rank : Nat)
    (firstBounds : firstLow ≤ firstHigh) (secondBounds : secondLow ≤ secondHigh)
    (firstBefore : cumulative (firstLow - 1) = 0) (secondBefore : cumulative (secondLow - 1) = 0)
    (firstUpper : rank < cumulative firstHigh) (secondUpper : rank < cumulative secondHigh)
    (monotone : MonotoneCount cumulative) :
    selectCoordinate firstLow firstHigh cumulative rank = selectCoordinate secondLow secondHigh cumulative rank := by
  have first := selected_section firstLow firstHigh cumulative rank firstBounds firstBefore firstUpper monotone
  have second := selected_section secondLow secondHigh cumulative rank secondBounds secondBefore secondUpper monotone
  exact section_coordinate_unique cumulative monotone rank _ _
    ⟨first.2.2.1, first.2.2.2⟩ ⟨second.2.2.1, second.2.2.2⟩

/-- One finite coordinate entry and its continuation. -/
abbrev Section (α : Type) := Int × α

/-- Distinct sections have distinct coordinate values. -/
def UniqueCoordinates (sections : List (Section α)) : Prop :=
  sections.Pairwise (fun left right => left.1 ≠ right.1)

/-- The total number of completions in a finite entry table. -/
def sectionTotal (count : α → Nat) : List (Section α) → Nat
  | [] => 0
  | (_, child) :: rest => count child + sectionTotal count rest

/-- Count the completions whose next coordinate is at most the supplied bound. -/
def through (count : α → Nat) : List (Section α) → Int → Nat
  | [], _ => 0
  | (coordinate, child) :: rest, bound =>
      (if coordinate ≤ bound then count child else 0) + through count rest bound

/-- Count the completions at one exact next-coordinate value. -/
def atCoordinate (count : α → Nat) : List (Section α) → Int → Nat
  | [], _ => 0
  | (coordinate, child) :: rest, wanted =>
      (if coordinate = wanted then count child else 0) + atCoordinate count rest wanted

/-- Find the continuation for one coordinate. -/
def childAt (coordinate : Int) : List (Section α) → Option α
  | [] => none
  | (key, child) :: rest => if coordinate = key then some child else childAt coordinate rest

/-- Finite completion counts are monotone by their concrete definition. -/
theorem through_monotone (count : α → Nat) (sections : List (Section α)) :
    MonotoneCount (through count sections) := by
  intro low high bounds
  induction sections with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
      rcases entry with ⟨coordinate, child⟩
      simp only [through]
      split <;> split <;> omega

/-- Cumulative counts are bounded by the total number of completions. -/
theorem through_le_total (count : α → Nat) (sections : List (Section α)) (bound : Int) :
    through count sections bound ≤ sectionTotal count sections := by
  induction sections with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
      rcases entry with ⟨coordinate, child⟩
      simp only [through, sectionTotal]
      split <;> omega

/-- An integer cumulative count increases by exactly the entry at that integer. -/
theorem through_step (count : α → Nat) (sections : List (Section α)) (coordinate : Int) :
    through count sections coordinate = through count sections (coordinate - 1) +
      atCoordinate count sections coordinate := by
  induction sections with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, child⟩
      by_cases before : key ≤ coordinate - 1
      · have below : key ≤ coordinate := by omega
        have different : key ≠ coordinate := by omega
        simp [through, atCoordinate, before, below, different, ih]
        omega
      · by_cases same : key = coordinate
        · subst key
          simp [through, atCoordinate, before, ih]
          omega
        · have above : ¬key ≤ coordinate := by omega
          simp [through, atCoordinate, before, same, above, ih]

/-- If no entry has a coordinate, that coordinate has zero completions. -/
theorem atCoordinate_zero (count : α → Nat) (sections : List (Section α)) (coordinate : Int)
    (absent : ∀ entry ∈ sections, entry.1 ≠ coordinate) :
    atCoordinate count sections coordinate = 0 := by
  induction sections with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, child⟩
      have head : key ≠ coordinate := absent (key, child) (by simp)
      simp [atCoordinate, head,
        ih (fun entry hm => absent entry (List.mem_cons_of_mem _ hm))]

/-- A unique entry table's point count equals the count of its lookup result. -/
theorem atCoordinate_lookup (count : α → Nat) (sections : List (Section α))
    (unique : UniqueCoordinates sections) (coordinate : Int) :
    atCoordinate count sections coordinate =
      (childAt coordinate sections).elim 0 count := by
  induction sections with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, child⟩
      obtain ⟨apart, tailUnique⟩ := List.pairwise_cons.mp unique
      by_cases same : coordinate = key
      · subst coordinate
        have absent : ∀ entry ∈ rest, entry.1 ≠ key := by
          intro entry hm he
          exact apart entry hm he.symm
        simp [atCoordinate, childAt, atCoordinate_zero count rest key absent]
      · have other : key ≠ coordinate := Ne.symm same
        simp [atCoordinate, childAt, same, other, ih tailUnique]

/-- Every successful entry lookup names a member of the finite table. -/
theorem childAt_mem (sections : List (Section α)) (coordinate : Int) (child : α)
    (found : childAt coordinate sections = some child) : (coordinate, child) ∈ sections := by
  induction sections with
  | nil => simp [childAt] at found
  | cons entry rest ih =>
      rcases entry with ⟨key, head⟩
      simp only [childAt] at found
      split at found
      · next same => cases found; subst coordinate; simp
      · exact List.mem_cons_of_mem _ (ih found)

/-- In a unique table, every listed coordinate retrieves its own continuation. -/
theorem childAt_of_mem (sections : List (Section α)) (unique : UniqueCoordinates sections)
    (coordinate : Int) (child : α) (member : (coordinate, child) ∈ sections) :
    childAt coordinate sections = some child := by
  induction sections with
  | nil => simp at member
  | cons entry rest ih =>
      rcases entry with ⟨key, head⟩
      obtain ⟨apart, tailUnique⟩ := List.pairwise_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · cases same
        simp [childAt]
      · have different : coordinate ≠ key := Ne.symm (apart (coordinate, child) member)
        simp [childAt, different, ih tailUnique member]

/-- A finite lower enclosure of the coordinate support. -/
def lowerBound : List (Section α) → Int
  | [] => 0
  | (coordinate, _) :: rest => min coordinate (lowerBound rest)

/-- A finite upper enclosure of the coordinate support. -/
def upperBound : List (Section α) → Int
  | [] => 0
  | (coordinate, _) :: rest => max coordinate (upperBound rest)

/-- The enclosures remain ordered even for an empty entry table. -/
theorem bounds_ordered (sections : List (Section α)) : lowerBound sections ≤ upperBound sections := by
  induction sections with
  | nil => exact Int.le_refl _
  | cons entry rest ih =>
      rcases entry with ⟨coordinate, child⟩
      simp only [lowerBound, upperBound]
      omega

/-- Every member lies within the finite coordinate enclosure. -/
theorem member_bounds (sections : List (Section α)) (coordinate : Int) (child : α)
    (member : (coordinate, child) ∈ sections) :
    lowerBound sections ≤ coordinate ∧ coordinate ≤ upperBound sections := by
  induction sections with
  | nil => simp at member
  | cons entry rest ih =>
      rcases entry with ⟨key, head⟩
      simp only [lowerBound, upperBound]
      rcases List.mem_cons.mp member with same | member
      · cases same; omega
      · have hb := ih member; omega

/-- No completion lies below a lower enclosure. -/
theorem through_below (count : α → Nat) (sections : List (Section α)) (low : Int)
    (bounds : ∀ entry ∈ sections, low ≤ entry.1) :
    through count sections (low - 1) = 0 := by
  induction sections with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨coordinate, child⟩
      have above : ¬coordinate ≤ low - 1 := by have := bounds (coordinate, child) (by simp); omega
      simp [through, above, ih (fun entry hm => bounds entry (List.mem_cons_of_mem _ hm))]

/-- An upper enclosure includes all completions. -/
theorem through_above (count : α → Nat) (sections : List (Section α)) (high : Int)
    (bounds : ∀ entry ∈ sections, entry.1 ≤ high) :
    through count sections high = sectionTotal count sections := by
  induction sections with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨coordinate, child⟩
      have below : coordinate ≤ high := bounds (coordinate, child) (by simp)
      simp [through, sectionTotal, below,
        ih (fun entry hm => bounds entry (List.mem_cons_of_mem _ hm))]

/-- Select a coordinate entry and retain the residual rank of its continuation. -/
def selectSection (count : α → Nat) (sections : List (Section α)) (rank : Nat) :
    Option (Int × α × Nat) :=
  if rank < sectionTotal count sections then
    let coordinate := selectCoordinate (lowerBound sections) (upperBound sections) (through count sections) rank
    match childAt coordinate sections with
    | none => none
    | some child => some (coordinate, child, rank - through count sections (coordinate - 1))
  else none

/-- Every valid rank selects a live entry with an in-range residual rank. -/
theorem selectSection_exists (count : α → Nat) (sections : List (Section α))
    (unique : UniqueCoordinates sections) (rank : Nat)
    (valid : rank < sectionTotal count sections) :
    ∃ coordinate child residual,
      selectSection count sections rank = some (coordinate, child, residual) ∧
      childAt coordinate sections = some child ∧ residual < count child ∧
      through count sections (coordinate - 1) + residual = rank := by
  let coordinate := selectCoordinate (lowerBound sections) (upperBound sections) (through count sections) rank
  have before := through_below count sections (lowerBound sections)
    (fun entry hm => (member_bounds sections entry.1 entry.2 hm).1)
  have upper := through_above count sections (upperBound sections)
    (fun entry hm => (member_bounds sections entry.1 entry.2 hm).2)
  have selected := selected_section (lowerBound sections) (upperBound sections) (through count sections) rank
    (bounds_ordered sections) before (by simpa [upper] using valid) (through_monotone count sections)
  have residual := residual_rank_range (lowerBound sections) (upperBound sections) (through count sections) rank
    (bounds_ordered sections) before (by simpa [upper] using valid) (through_monotone count sections)
  have step := through_step count sections coordinate
  have lookup := atCoordinate_lookup count sections unique coordinate
  cases found : childAt coordinate sections with
  | none =>
      rw [found] at lookup
      simp only [Option.elim_none] at lookup
      dsimp only at residual
      change rank - through count sections (coordinate - 1) <
        through count sections coordinate - through count sections (coordinate - 1) ∧ _ at residual
      omega
  | some child =>
      rw [found] at lookup
      simp only [Option.elim_some] at lookup
      refine ⟨coordinate, child, rank - through count sections (coordinate - 1), ?_, found, ?_, residual.2⟩
      · simp [selectSection, valid, coordinate, found]
      · change rank - through count sections (coordinate - 1) <
          through count sections coordinate - through count sections (coordinate - 1) ∧ _ at residual
        omega

/-- A listed continuation and a valid residual rank reconstruct their unique global rank. -/
theorem selectSection_encode (count : α → Nat) (sections : List (Section α))
    (unique : UniqueCoordinates sections) (coordinate : Int) (child : α)
    (found : childAt coordinate sections = some child) (residual : Nat) (valid : residual < count child) :
    selectSection count sections (through count sections (coordinate - 1) + residual) =
      some (coordinate, child, residual) := by
  have step := through_step count sections coordinate
  have pointCount := atCoordinate_lookup count sections unique coordinate
  rw [found] at pointCount
  simp only [Option.elim_some] at pointCount
  have interval : through count sections (coordinate - 1) ≤ through count sections (coordinate - 1) + residual ∧
      through count sections (coordinate - 1) + residual < through count sections coordinate := by omega
  have rankValid : through count sections (coordinate - 1) + residual < sectionTotal count sections :=
    Nat.lt_of_lt_of_le interval.2 (through_le_total count sections coordinate)
  have before := through_below count sections (lowerBound sections)
    (fun entry hm => (member_bounds sections entry.1 entry.2 hm).1)
  have upper := through_above count sections (upperBound sections)
    (fun entry hm => (member_bounds sections entry.1 entry.2 hm).2)
  have selected := selected_section (lowerBound sections) (upperBound sections) (through count sections)
    (through count sections (coordinate - 1) + residual) (bounds_ordered sections) before
    (by simpa [upper] using rankValid) (through_monotone count sections)
  have same := section_coordinate_unique (through count sections) (through_monotone count sections)
    _ _ coordinate ⟨selected.2.2.1, selected.2.2.2⟩ interval
  simp [selectSection, rankValid, same, found]

/-- A successful section selection can only come from an in-range rank. -/
theorem selectSection_valid (count : α → Nat) (sections : List (Section α)) (rank : Nat)
    (result : Int × α × Nat) (found : selectSection count sections rank = some result) :
    rank < sectionTotal count sections := by
  unfold selectSection at found
  split at found
  · assumption
  · contradiction

/-- A finite integer-point tree, with one section level per variable. -/
abbrev Sections : Nat → Type
  | 0 => Bool
  | variables + 1 => List (Section (Sections variables))

/-- Count all accepted integer tuples in the concrete section tree. -/
def pointCount : (variables : Nat) → Sections variables → Nat
  | 0, accepted => if accepted then 1 else 0
  | variables + 1, sections => sectionTotal (pointCount variables) sections

/-- Each level has one continuation per coordinate and valid children. -/
def WellFormed : (variables : Nat) → Sections variables → Prop
  | 0, _ => True
  | variables + 1, sections => UniqueCoordinates sections ∧
      ∀ entry ∈ sections, WellFormed variables entry.2

/-- A tuple follows an existing coordinate section at every variable. -/
def Admits : (variables : Nat) → Sections variables → List Int → Prop
  | 0, accepted, [] => accepted = true
  | variables + 1, sections, coordinate :: rest =>
      ∃ child, (coordinate, child) ∈ sections ∧ Admits variables child rest
  | _, _, _ => False

/-- Decode variables left to right by cumulative completion counts. -/
def pointAt : (variables : Nat) → Sections variables → Nat → Option (List Int)
  | 0, accepted, rank => if accepted && rank == 0 then some [] else none
  | variables + 1, sections, rank =>
      (selectSection (pointCount variables) sections rank).bind fun (coordinate, child, residual) =>
        (pointAt variables child residual).map (coordinate :: ·)

/-- Add the counts of earlier-coordinate completions at each prefix. -/
def pointRank : (variables : Nat) → Sections variables → List Int → Option Nat
  | 0, accepted, [] => if accepted then some 0 else none
  | variables + 1, sections, coordinate :: rest =>
      (childAt coordinate sections).bind fun child =>
        (pointRank variables child rest).map fun residual =>
          through (pointCount variables) sections (coordinate - 1) + residual
  | _, _, _ => none

/-- Every valid global rank decodes to an admitted tuple and is recovered by ranking it. -/
theorem pointAt_exists (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (rank : Nat) (valid : rank < pointCount variables sections) :
    ∃ tuple, pointAt variables sections rank = some tuple ∧
      Admits variables sections tuple ∧ pointRank variables sections tuple = some rank := by
  induction variables generalizing rank with
  | zero =>
      cases sections with
      | false => simp [pointCount] at valid
      | true =>
          have hr : rank = 0 := by simpa [pointCount] using valid
          subst rank
          exact ⟨[], rfl, rfl, rfl⟩
  | succ variables ih =>
      obtain ⟨coordinate, child, residual, selected, found, residualValid, rankEq⟩ :=
        selectSection_exists (pointCount variables) sections wellFormed.1 rank valid
      have member := childAt_mem sections coordinate child found
      obtain ⟨tuple, decoded, admitted, ranked⟩ := ih child (wellFormed.2 _ member) residual residualValid
      refine ⟨coordinate :: tuple, ?_, ⟨child, member, admitted⟩, ?_⟩
      · simp [pointAt, selected, decoded]
      · simp [pointRank, found, ranked, rankEq]

/-- Every admitted tuple is reached at a valid rank computed from its concrete sections. -/
theorem pointRank_exists (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (tuple : List Int) (admitted : Admits variables sections tuple) :
    ∃ rank, rank < pointCount variables sections ∧ pointRank variables sections tuple = some rank ∧
      pointAt variables sections rank = some tuple := by
  induction variables generalizing tuple with
  | zero =>
      cases tuple with
      | nil =>
          have ht : sections = true := admitted
          subst sections
          exact ⟨0, by decide, rfl, rfl⟩
      | cons head tail => contradiction
  | succ variables ih =>
      cases tuple with
      | nil => contradiction
      | cons coordinate rest =>
          obtain ⟨child, member, childAdmitted⟩ := admitted
          have found := childAt_of_mem sections wellFormed.1 coordinate child member
          obtain ⟨residual, residualValid, ranked, decoded⟩ :=
            ih child (wellFormed.2 _ member) rest childAdmitted
          have selected := selectSection_encode (pointCount variables) sections wellFormed.1
            coordinate child found residual residualValid
          refine ⟨through (pointCount variables) sections (coordinate - 1) + residual,
            selectSection_valid _ _ _ _ selected, ?_, ?_⟩
          · simp [pointRank, found, ranked]
          · simp [pointAt, selected, decoded]

/-- The rank decoder rejects every out-of-range input. -/
theorem pointAt_rank_valid (variables : Nat) (sections : Sections variables) (rank : Nat)
    (tuple : List Int) (decoded : pointAt variables sections rank = some tuple) :
    rank < pointCount variables sections := by
  cases variables with
  | zero =>
      unfold pointAt at decoded
      split at decoded
      · next h =>
          have hs := Bool.and_eq_true _ _ |>.mp h
          have hr : rank = 0 := by simpa using hs.2
          simp [pointCount, hs.1, hr]
      · contradiction
  | succ variables =>
      cases selected : selectSection (pointCount variables) sections rank with
      | none => simp [pointAt, selected] at decoded
      | some result => exact selectSection_valid _ _ _ _ selected

/-- A successful rank query certifies tuple membership. -/
theorem pointRank_admits (variables : Nat) (sections : Sections variables) (tuple : List Int)
    (rank : Nat) (ranked : pointRank variables sections tuple = some rank) : Admits variables sections tuple := by
  induction variables generalizing tuple rank with
  | zero =>
      cases tuple with
      | nil =>
          cases sections <;> simp [pointRank, Admits] at *
      | cons head tail => simp [pointRank] at ranked
  | succ variables ih =>
      cases tuple with
      | nil => simp [pointRank] at ranked
      | cons coordinate rest =>
          cases found : childAt coordinate sections with
          | none => simp [pointRank, found] at ranked
          | some child =>
              cases tailRank : pointRank variables child rest with
              | none => simp [pointRank, found, tailRank] at ranked
              | some residual =>
                  exact ⟨child, childAt_mem sections coordinate child found, ih child rest residual tailRank⟩

/-- Ranking a decoded tuple recovers the supplied global rank. -/
theorem pointRank_pointAt (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (rank : Nat) (tuple : List Int)
    (decoded : pointAt variables sections rank = some tuple) :
    pointRank variables sections tuple = some rank := by
  obtain ⟨other, found, admitted, ranked⟩ := pointAt_exists variables sections wellFormed rank
    (pointAt_rank_valid variables sections rank tuple decoded)
  have heq : other = tuple := Option.some.inj (found.symm.trans decoded)
  simpa [heq] using ranked

/-- Decoding a successful rank query returns exactly the original tuple. -/
theorem pointAt_pointRank (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (tuple : List Int) (rank : Nat)
    (ranked : pointRank variables sections tuple = some rank) :
    pointAt variables sections rank = some tuple := by
  obtain ⟨other, valid, found, decoded⟩ := pointRank_exists variables sections wellFormed tuple
    (pointRank_admits variables sections tuple rank ranked)
  have heq : other = rank := Option.some.inj (found.symm.trans ranked)
  simpa [heq] using decoded

/-- Successful rank queries return an in-range rank. -/
theorem pointRank_range (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (tuple : List Int) (rank : Nat)
    (ranked : pointRank variables sections tuple = some rank) : rank < pointCount variables sections := by
  exact pointAt_rank_valid variables sections rank tuple (pointAt_pointRank variables sections wellFormed tuple rank ranked)

/-- Point membership is exactly the domain of the executable rank query. -/
theorem admits_iff_ranked (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (tuple : List Int) :
    Admits variables sections tuple ↔ ∃ rank, pointRank variables sections tuple = some rank := by
  constructor
  · intro admitted
    obtain ⟨rank, _, ranked, _⟩ := pointRank_exists variables sections wellFormed tuple admitted
    exact ⟨rank, ranked⟩
  · rintro ⟨rank, ranked⟩
    exact pointRank_admits variables sections tuple rank ranked

/-- Each admitted tuple has exactly the declared number of coordinates. -/
theorem admitted_length (variables : Nat) (sections : Sections variables) (tuple : List Int)
    (admitted : Admits variables sections tuple) : tuple.length = variables := by
  induction variables generalizing tuple with
  | zero => cases tuple <;> simp [Admits] at *
  | succ variables ih =>
      cases tuple with
      | nil => contradiction
      | cons coordinate rest =>
          obtain ⟨child, _, childAdmitted⟩ := admitted
          simp [ih child rest childAdmitted]

/-- Every successfully decoded tuple has exactly the declared variable count. -/
theorem pointAt_length (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (rank : Nat) (tuple : List Int)
    (decoded : pointAt variables sections rank = some tuple) : tuple.length = variables := by
  exact admitted_length variables sections tuple
    (pointRank_admits variables sections tuple rank (pointRank_pointAt variables sections wellFormed rank tuple decoded))

/-- Enumerate the concrete section tree without using ranks or binary search. -/
def tuples : (variables : Nat) → Sections variables → List (List Int)
  | 0, accepted => if accepted then [[]] else []
  | variables + 1, sections => sections.flatMap fun (coordinate, child) =>
      (tuples variables child).map (coordinate :: ·)

/-- Concrete completion counts equal the size of the independent enumeration. -/
theorem tuples_length (variables : Nat) (sections : Sections variables) :
    (tuples variables sections).length = pointCount variables sections := by
  induction variables with
  | zero => cases sections <;> rfl
  | succ variables ih =>
      induction sections with
      | nil => rfl
      | cons entry rest ihr =>
          rcases entry with ⟨coordinate, child⟩
          change ((tuples variables child).map (coordinate :: ·) ++ tuples (variables + 1) rest).length = _
          rw [List.length_append, List.length_map, ih, ihr]
          rfl

/-- The independent enumeration contains exactly the admitted tuples. -/
theorem mem_tuples_iff (variables : Nat) (sections : Sections variables) (tuple : List Int) :
    tuple ∈ tuples variables sections ↔ Admits variables sections tuple := by
  induction variables generalizing tuple with
  | zero => cases sections <;> cases tuple <;> simp [tuples, Admits]
  | succ variables ih =>
      cases tuple with
      | nil => simp [tuples, Admits, List.mem_flatMap, List.mem_map]
      | cons coordinate rest =>
          simp only [tuples, List.mem_flatMap, List.mem_map, Admits]
          constructor
          · rintro ⟨⟨key, child⟩, member, tail, htail, equal⟩
            obtain ⟨headEq, tailEq⟩ := List.cons.inj equal
            change key = coordinate at headEq
            subst key
            subst tail
            exact ⟨child, member, (ih child rest).mp htail⟩
          · rintro ⟨child, member, hrest⟩
            exact ⟨(coordinate, child), member, rest, (ih child rest).mpr hrest, rfl⟩

/-- Decode a valid finite replay rank without an optional result. -/
def decodeList (variables : Nat) (sections : Sections variables)
    (rank : Fin (pointCount variables sections)) : List Int :=
  (pointAt variables sections rank.val).getD []

/-- The total decoder agrees with the checked rank decoder. -/
theorem pointAt_decodeList (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (rank : Fin (pointCount variables sections)) :
    pointAt variables sections rank.val = some (decodeList variables sections rank) := by
  obtain ⟨tuple, decoded, _, _⟩ := pointAt_exists variables sections wellFormed rank.val rank.isLt
  simp [decodeList, decoded]

/-- Total decoding produces an admitted tuple. -/
theorem decodeList_admitted (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (rank : Fin (pointCount variables sections)) :
    Admits variables sections (decodeList variables sections rank) := by
  exact pointRank_admits variables sections _ rank.val
    (pointRank_pointAt variables sections wellFormed _ _ (pointAt_decodeList variables sections wellFormed rank))

/-- Every admitted tuple is the decoding of a valid finite rank. -/
theorem decodeList_surjective (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (tuple : List Int) (admitted : Admits variables sections tuple) :
    ∃ rank : Fin (pointCount variables sections), decodeList variables sections rank = tuple := by
  obtain ⟨rank, valid, _, decoded⟩ := pointRank_exists variables sections wellFormed tuple admitted
  exact ⟨⟨rank, valid⟩, by simp [decodeList, decoded]⟩

/-- Distinct finite ranks decode to distinct admitted tuples. -/
theorem decodeList_injective (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) : Function.Injective (decodeList variables sections) := by
  intro left right same
  have hl := pointRank_pointAt variables sections wellFormed _ _ (pointAt_decodeList variables sections wellFormed left)
  have hr := pointRank_pointAt variables sections wellFormed _ _ (pointAt_decodeList variables sections wellFormed right)
  rw [same] at hl
  apply Fin.ext
  exact Option.some.inj (hl.symm.trans hr)

/-- Read a fixed-length integer tuple as the finite function used by `Points`. -/
def tupleFunction (variables : Nat) (tuple : List Int) : Fin variables → Int :=
  fun index => tuple[index.val]?.getD 0

/-- Conversion of a finite function to a list and back preserves every coordinate. -/
theorem tupleFunction_ofFn (variables : Nat) (tuple : Fin variables → Int) :
    tupleFunction variables (List.ofFn tuple) = tuple := by
  funext index
  simp [tupleFunction, index.isLt]

/-- Conversion of a correctly sized tuple to a finite function preserves its list. -/
theorem ofFn_tupleFunction (variables : Nat) (tuple : List Int) (length : tuple.length = variables) :
    List.ofFn (tupleFunction variables tuple) = tuple := by
  subst variables
  have hfun : tupleFunction tuple.length tuple = fun index : Fin tuple.length => tuple[index.val] := by
    funext index
    simp [tupleFunction]
  rw [hfun, List.ofFn_getElem]

/-- Supply the existing point-closure interface with a concrete verified decoder. -/
def points (variables : Nat) (sections : Sections variables) : ZeroSize.Points variables where
  count := pointCount variables sections
  decode rank := tupleFunction variables (decodeList variables sections rank)

/-- The verified table has exact coverage and no duplicate tuple ranks. -/
theorem points_exact (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) :
    ZeroSize.ExactPoints (points variables sections)
      (fun tuple => Admits variables sections (List.ofFn tuple)) := by
  constructor
  · intro tuple
    constructor
    · intro admitted
      obtain ⟨rank, decoded⟩ := decodeList_surjective variables sections wellFormed (List.ofFn tuple) admitted
      refine ⟨rank, ?_⟩
      change tupleFunction variables (decodeList variables sections rank) = tuple
      rw [decoded, tupleFunction_ofFn]
    · rintro ⟨rank, decoded⟩
      change tupleFunction variables (decodeList variables sections rank) = tuple at decoded
      have admitted := decodeList_admitted variables sections wellFormed rank
      have length := admitted_length variables sections _ admitted
      rw [← decoded, ofFn_tupleFunction variables _ length]
      exact admitted
  · intro left right same
    apply decodeList_injective variables sections wellFormed
    have hl := admitted_length variables sections _ (decodeList_admitted variables sections wellFormed left)
    have hr := admitted_length variables sections _ (decodeList_admitted variables sections wellFormed right)
    have lists := congrArg List.ofFn same
    change List.ofFn (tupleFunction variables (decodeList variables sections left)) =
      List.ofFn (tupleFunction variables (decodeList variables sections right)) at lists
    simpa [ofFn_tupleFunction variables _ hl, ofFn_tupleFunction variables _ hr] using lists

/-- Closing source outcomes over this table needs no unproved exact-points premise. -/
theorem closePoints_exact {Value : Type} (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections)
    (sources : List (ZeroSize.OpenOutcome variables Value)) (size : Nat) (value : Value) :
    (size, value) ∈ ZeroSize.closePoints (points variables sections) sources ↔
      ∃ source, source ∈ sources ∧ ∃ tuple,
        Admits variables sections (List.ofFn tuple) ∧
        size = source.1 + variables ∧ value = source.2 tuple := by
  exact ZeroSize.closePoints_exact (points variables sections) _ (points_exact variables sections wellFormed)
    sources size value

/-- Expose the next coordinate's offset and recursively computed residual rank. -/
theorem pointRank_cons_parts (variables : Nat) (sections : Sections (variables + 1))
    (coordinate : Int) (rest : List Int) (rank : Nat)
    (ranked : pointRank (variables + 1) sections (coordinate :: rest) = some rank) :
    ∃ child residual, childAt coordinate sections = some child ∧
      pointRank variables child rest = some residual ∧
      rank = through (pointCount variables) sections (coordinate - 1) + residual := by
  cases found : childAt coordinate sections with
  | none => simp [pointRank, found] at ranked
  | some child =>
      cases tailRank : pointRank variables child rest with
      | none => simp [pointRank, found, tailRank] at ranked
      | some residual =>
          refine ⟨child, residual, rfl, tailRank, ?_⟩
          have heq : through (pointCount variables) sections (coordinate - 1) + residual = rank := by
            simpa [pointRank, found, tailRank] using ranked
          exact heq.symm

/-- A tuple's lexicographic rank lies inside its first-coordinate completion interval. -/
theorem pointRank_coordinate_interval (variables : Nat) (sections : Sections (variables + 1))
    (wellFormed : WellFormed (variables + 1) sections) (coordinate : Int) (rest : List Int) (rank : Nat)
    (ranked : pointRank (variables + 1) sections (coordinate :: rest) = some rank) :
    through (pointCount variables) sections (coordinate - 1) ≤ rank ∧
      rank < through (pointCount variables) sections coordinate := by
  obtain ⟨child, residual, found, tailRank, rankEq⟩ :=
    pointRank_cons_parts variables sections coordinate rest rank ranked
  have member := childAt_mem sections coordinate child found
  have residualValid := pointRank_range variables child (wellFormed.2 _ member) rest residual tailRank
  have step := through_step (pointCount variables) sections coordinate
  have atCount := atCoordinate_lookup (pointCount variables) sections wellFormed.1 coordinate
  rw [found] at atCount
  simp only [Option.elim_some] at atCount
  omega

/-- Lexicographically smaller admitted tuples have strictly smaller ranks. -/
theorem pointRank_lex (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (left right : List Int) (leftRank rightRank : Nat)
    (hl : pointRank variables sections left = some leftRank)
    (hr : pointRank variables sections right = some rightRank)
    (ordered : List.Lex (· < ·) left right) : leftRank < rightRank := by
  induction variables generalizing left right leftRank rightRank with
  | zero =>
      have ll := admitted_length 0 sections left (pointRank_admits 0 sections left leftRank hl)
      have lr := admitted_length 0 sections right (pointRank_admits 0 sections right rightRank hr)
      have el : left = [] := List.length_eq_zero_iff.mp ll
      have er : right = [] := List.length_eq_zero_iff.mp lr
      subst left
      subst right
      cases ordered
  | succ variables ih =>
      cases left with
      | nil => simp [pointRank] at hl
      | cons lc ls =>
          cases right with
          | nil => simp [pointRank] at hr
          | cons rc rs =>
              cases ordered with
              | rel before =>
                  have li := pointRank_coordinate_interval variables sections wellFormed lc ls leftRank hl
                  have ri := pointRank_coordinate_interval variables sections wellFormed rc rs rightRank hr
                  have monotone := through_monotone (pointCount variables) sections lc (rc - 1) (by omega)
                  omega
              | cons tailBefore =>
                  obtain ⟨child, childRank, found, tailLeft, rankLeft⟩ :=
                    pointRank_cons_parts variables sections lc ls leftRank hl
                  obtain ⟨other, otherRank, foundOther, tailRight, rankRight⟩ :=
                    pointRank_cons_parts variables sections lc rs rightRank hr
                  have same : other = child := Option.some.inj (foundOther.symm.trans found)
                  subst other
                  have member := childAt_mem sections lc child found
                  have smaller := ih child (wellFormed.2 _ member) ls rs childRank otherRank tailLeft tailRight tailBefore
                  omega

/-- Rank order is exactly lexicographic order in the declared variable order. -/
theorem pointRank_order_iff (variables : Nat) (sections : Sections variables)
    (wellFormed : WellFormed variables sections) (left right : List Int) (leftRank rightRank : Nat)
    (hl : pointRank variables sections left = some leftRank)
    (hr : pointRank variables sections right = some rightRank) :
    leftRank < rightRank ↔ List.Lex (· < ·) left right := by
  constructor
  · intro before
    classical
    by_cases forward : List.Lex (· < ·) left right
    · exact forward
    · by_cases backward : List.Lex (· < ·) right left
      · have opposite := pointRank_lex variables sections wellFormed right left rightRank leftRank hr hl backward
        omega
      · have same : left = right := List.lex_trichotomous (by intro a b hn hm; omega) backward forward
        subst right
        have ranksEqual : leftRank = rightRank := Option.some.inj (hl.symm.trans hr)
        omega
  · exact pointRank_lex variables sections wellFormed left right leftRank rightRank hl hr

/-- Exact natural counts give exactly the rational comparison used by Haskell. -/
theorem rational_count_predicate (rank count : Nat) :
    decide ((rank : Rat) < (count : Rat)) = decide (rank < count) := by
  simp [Rat.natCast_lt_natCast]

/-- Extracting the numerator of an exact integer count preserves its integer value. -/
theorem exact_count_numerator (count : Nat) : (count : Rat).num = (count : Int) := rfl

/-- The Haskell integer residual agrees with natural subtraction on a valid rank. -/
theorem integer_residual (rank earlier : Nat) (valid : earlier ≤ rank) :
    (rank : Int) - (earlier : Rat).num = ((rank - earlier : Nat) : Int) := by
  rw [exact_count_numerator]
  omega

/-- A finite example with negative coordinates, gaps, and unsorted stored sections. -/
def exampleSections : Sections 2 :=
  [(4, [(3, true), (-2, true)]), (-5, [(7, true)])]

/-- Stored section order does not change lexicographic decoding. -/
theorem example_lexicographic_decoding :
    pointCount 2 exampleSections = 3 ∧
    pointAt 2 exampleSections 0 = some [-5, 7] ∧
    pointAt 2 exampleSections 1 = some [4, -2] ∧
    pointAt 2 exampleSections 2 = some [4, 3] ∧
    pointRank 2 exampleSections [4, -2] = some 1 ∧
    pointRank 2 exampleSections [4, 0] = none := by decide +kernel

/-- Zero variables have one empty tuple precisely when the formula is true. -/
theorem zero_variables :
    pointCount 0 true = 1 ∧ pointAt 0 true 0 = some [] ∧
    pointRank 0 true [] = some 0 ∧ pointCount 0 false = 0 := by decide +kernel

end MicroCFTA.LatticeRank
