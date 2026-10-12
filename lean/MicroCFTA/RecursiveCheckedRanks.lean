import MicroCFTA.CompositeCheckedRanks
import MicroCFTA.SizedRank

/-!
# Recursive checked positions and a guarded recursive family

The product adapter uses the source split decoder and checked Cartesian
product. The guarded family has one empty alternative and any finite number
of paid unary alternatives. It retains every private recursion and choice
node. Its inverse reads only the requested term. Its decoder uses class
counts and division. Neither operation enumerates earlier terms.
-/
namespace MicroCFTA.RecursiveCheckedRanks
open Language GeneratorCombinators IntegerTermViews SizedRank

/-- A class callback retains its size, class rank, and checked-symbol flag. -/
abbrev Checked := Position × Bool

/-- Source Cartesian candidates retain the conjunction of both certificates. -/
def productRows (left right : Nat → Nat) (first second : List Checked) : List Checked :=
  first.flatMap fun a => second.map fun b => (productPosition left right a.1 b.1, a.2 && b.2)

/-- Source product selection first recovers the size split and both local ranks. -/
def selectProduct (left right : Nat → Nat)
    (first second : Position → Option (Term (Label Symbol))) (position : Position) :
    Option (Term (Label Symbol)) := do
  let pair ← productSplit left right position
  let f ← first pair.1
  let x ← second pair.2
  pure (.node .apply [f, x])

/-- A true product flag decodes the requested pair at its computed class position. -/
theorem product_checked (left right : Nat → Nat)
    (first second : Position → Option (Term (Label Symbol)))
    (firstRows secondRows : List Checked) (f x : Term (Label Symbol))
    (firstSound : ∀ p, (p, true) ∈ firstRows → p.rank < left p.size ∧ first p = some f)
    (secondSound : ∀ p, (p, true) ∈ secondRows → p.rank < right p.size ∧ second p = some x)
    (position : Position) (member : (position, true) ∈ productRows left right firstRows secondRows) :
    selectProduct left right first second position = some (.node .apply [f, x]) := by
  obtain ⟨a, am, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨b, bm, same⟩ := List.mem_map.mp mapped
  have both : a.2 = true ∧ b.2 = true := by
    have flags := congrArg Prod.snd same
    simpa only [Bool.and_eq_true] using flags
  have ha := firstSound a.1 (by rw [← both.1]; exact am)
  have hb := secondSound b.1 (by rw [← both.2]; exact bm)
  have positionSame : productPosition left right a.1 b.1 = position := congrArg Prod.fst same
  rw [← positionSame]
  simp [selectProduct, productSplit_productPosition left right a.1 b.1 ha.1 hb.1, ha.2, hb.2]

/-- Each pair of certified children occurs in the source product callback. -/
theorem product_complete (left right : Nat → Nat) (firstRows secondRows : List Checked)
    (first second : Position) (hm : (first, true) ∈ firstRows) (hn : (second, true) ∈ secondRows) :
    (productPosition left right first second, true) ∈ productRows left right firstRows secondRows :=
  List.mem_flatMap.mpr ⟨(first, true), hm, List.mem_map.mpr ⟨(second, true), hn, rfl⟩⟩

/-- The source pay adapter increments only the size component. -/
def payRows (rows : List Checked) : List Checked :=
  rows.map fun row => (⟨row.1.size + 1, row.1.rank⟩, row.2)

/-- Paid class selection removes exactly the added size unit. -/
def selectPay (select : Position → Option α) (position : Position) : Option α :=
  match position.size with
  | 0 => none
  | size + 1 => select ⟨size, position.rank⟩

/-- Pay cannot turn a sound certificate into an incorrect replay. -/
theorem pay_checked (select : Position → Option α) (rows : List Checked) (value : α)
    (sound : ∀ p, (p, true) ∈ rows → select p = some value)
    (position : Position) (member : (position, true) ∈ payRows rows) :
    selectPay select position = some value := by
  obtain ⟨⟨p, flag⟩, present, same⟩ := List.mem_map.mp member
  have flags : flag = true := congrArg Prod.snd same
  subst flag
  have positions : (⟨p.size + 1, p.rank⟩ : Position) = position := congrArg Prod.fst same
  rw [← positions]
  simpa [selectPay] using sound p present


/-- Source choice positions add all earlier same-size class counts. -/
def choiceRow (counts : List (Nat → Nat)) (branch : Nat) (row : Checked) : Checked :=
  (⟨row.1.size, choicePosition (counts.map fun count => count row.1.size) branch row.1.rank⟩, row.2)

/-- Direct source choice selection finds one branch and wraps its complete term. -/
def selectChoice (counts : List (Nat → Nat)) (selectors : List (Position → Option (Term (Label Symbol))))
    (position : Position) : Option (Term (Label Symbol)) := do
  let pair ← choiceSplit (counts.map fun count => count position.size) position.rank
  let select ← selectors[pair.1]?
  let child ← select ⟨position.size, pair.2⟩
  pure (.node (.choice pair.1) [child])

/-- An ordered choice preserves a certified child's exact class replay. -/
theorem choice_checked (counts : List (Nat → Nat)) (selectors : List (Position → Option (Term (Label Symbol))))
    (branch : Nat) (count : Nat → Nat) (select : Position → Option (Term (Label Symbol)))
    (countFound : counts[branch]? = some count) (selectFound : selectors[branch]? = some select)
    (position : Position) (term : Term (Label Symbol))
    (within : position.rank < count position.size) (selected : select position = some term) :
    selectChoice counts selectors (choiceRow counts branch (position, true)).1 =
      some (.node (.choice branch) [term]) := by
  have countAt : (counts.map fun count => count position.size)[branch]? = some (count position.size) := by
    simp [List.getElem?_map, countFound]
  have branchFound := choiceSplit_choicePosition _ branch position.rank (count position.size) countAt within
  simp [selectChoice, choiceRow, branchFound, selectFound, selected]

/-- A branch word stores the choice index of each unary constructor. -/
def ValidWord (arity : Nat) (word : List Nat) : Prop := ∀ branch ∈ word, branch < arity

/-- Source same-size choice offsets form a positional numeral. -/
def wordRank (arity : Nat) : List Nat → Nat
  | [] => 0
  | branch :: rest => branch * arity ^ rest.length + wordRank arity rest

/-- The member term keeps the recursion wrapper at each recursive occurrence. -/
def wordTerm (label : Nat → Symbol) : List Nat → Term (Label Symbol)
  | [] => .node .recursion [.node (.choice 0) [.node .pure []]]
  | branch :: rest => .node .recursion [.node (.choice (branch + 1))
      [.node (.user (label branch)) [wordTerm label rest]]]

/-- Each size class has the source sum of one equally sized block per branch. -/
def classCount (arity : Nat) : Nat → Nat
  | 0 => 1
  | size + 1 => (List.replicate arity (classCount arity size)).sum

/-- The recursive count recurrence has the exact finite coefficient at each size. -/
theorem class_count (arity size : Nat) : classCount arity size = arity ^ size := by
  induction size with
  | zero => simp [classCount]
  | succ size ih => simp [classCount, ih, Nat.pow_succ, Nat.mul_comm]


/-- The positive-size source choice has a zero base count and equal recursive blocks. -/
theorem unary_choice_offset (arity branch size rank : Nat) (within : branch < arity) :
    choicePosition (0 :: List.replicate arity (classCount arity size)) (branch + 1) rank =
      branch * classCount arity size + rank := by
  simp [choicePosition, List.take_replicate, Nat.min_eq_left (Nat.le_of_lt within)]

/-- Labelling a recursive occurrence keeps its complete private term as the sole child. -/
theorem unary_label_term (label : Nat → Symbol) (branch : Nat) (word : List Nat) :
    SupportTerms.labelTerm (label branch) (wordTerm label word) =
      .node (.user (label branch)) [wordTerm label word] := by
  cases word <;> simp [wordTerm, SupportTerms.labelTerm, SupportTerms.applicationTermChildren]

/-- Every valid branch word has a rank strictly inside its size class. -/
theorem word_rank_bound (arity : Nat) (word : List Nat) (valid : ValidWord arity word) :
    wordRank arity word < arity ^ word.length := by
  induction word with
  | nil => simp [wordRank]
  | cons branch rest ih =>
      have branchBound : branch < arity := valid branch (by simp)
      have restValid : ValidWord arity rest := fun b member => valid b (by simp [member])
      have rankBound := ih restValid
      have bounded := Probability.pairRank_lt branchBound rankBound
      simpa [wordRank, Probability.pairRank, Nat.pow_succ, Nat.mul_comm] using bounded

/-- Direct class selection uses division by the child class count. -/
def selectWord (arity : Nat) : Nat → Nat → Option (List Nat)
  | 0, rank => if rank = 0 then some [] else none
  | size + 1, rank =>
      if rank < arity ^ (size + 1) then
        (selectWord arity size (rank % arity ^ size)).map (rank / arity ^ size :: ·)
      else none

/-- The direct decoder reverses every computed valid word rank. -/
theorem select_word_rank (arity : Nat) (word : List Nat) (valid : ValidWord arity word) :
    selectWord arity word.length (wordRank arity word) = some word := by
  induction word with
  | nil => simp [selectWord, wordRank]
  | cons branch rest ih =>
      have restValid : ValidWord arity rest := fun b member => valid b (by simp [member])
      have rankBound := word_rank_bound arity rest restValid
      have split := Probability.split_pair rankBound (left := branch)
      have fstEq := congrArg Prod.fst split
      have sndEq := congrArg Prod.snd split
      simp only [Probability.splitRank, Probability.pairRank] at fstEq sndEq
      have wholeBound : branch * arity ^ rest.length + wordRank arity rest < arity ^ (rest.length + 1) :=
        word_rank_bound arity (branch :: rest) valid
      simp only [List.length_cons, selectWord, wordRank, wholeBound,
        ↓reduceIte, fstEq, sndEq, ih restValid, Option.map_some]

/-- A successful class decoder returns a valid word of the requested length and rank. -/
theorem select_word_sound (arity size rank : Nat) (word : List Nat)
    (selected : selectWord arity size rank = some word) :
    ValidWord arity word ∧ word.length = size ∧ wordRank arity word = rank := by
  induction size generalizing rank word with
  | zero =>
      simp only [selectWord] at selected
      split at selected
      next zero => subst rank; cases selected; simp [ValidWord, wordRank]
      next => cases selected
  | succ size ih =>
      simp only [selectWord] at selected
      split at selected
      next bounded =>
        obtain ⟨rest, found, same⟩ := Option.map_eq_some_iff.mp selected
        subst word
        obtain ⟨valid, lengthEq, rankEq⟩ := ih _ rest found
        have positive : 0 < arity ^ size := by
          have power : arity ^ (size + 1) = arity * arity ^ size := by rw [Nat.pow_succ, Nat.mul_comm]
          rw [power] at bounded
          apply Nat.pos_of_ne_zero
          intro zero
          simp [zero] at bounded
        have branchBound : rank / arity ^ size < arity := by
          apply (Nat.div_lt_iff_lt_mul positive).mpr
          simpa [Nat.pow_succ, Nat.mul_comm] using bounded
        refine ⟨?_, by simp [lengthEq], ?_⟩
        · intro b member
          rcases List.mem_cons.mp member with rfl | member
          · exact branchBound
          · exact valid b member
        · simp only [wordRank, lengthEq, rankEq]
          simpa only [Nat.mul_comm] using Nat.div_add_mod rank (arity ^ size)
      next => cases selected

/-- Every class rank has a direct decoder result. -/
theorem select_word_total (arity size rank : Nat) (within : rank < arity ^ size) :
    ∃ word, selectWord arity size rank = some word := by
  induction size generalizing rank with
  | zero =>
      have zero : rank = 0 := by simpa using within
      exact ⟨[], by simp [selectWord, zero]⟩
  | succ size ih =>
      have positive : 0 < arity ^ size := by
        apply Nat.pos_of_ne_zero
        intro zero
        simp [Nat.pow_succ, zero] at within
      obtain ⟨rest, selected⟩ := ih (rank % arity ^ size) (Nat.mod_lt _ positive)
      exact ⟨rank / arity ^ size :: rest, by simp [selectWord, within, selected]⟩

/-- A class position identifies exactly one word, even when user symbols repeat. -/
theorem word_rank_injective (arity : Nat) (first second : List Nat)
    (firstValid : ValidWord arity first) (secondValid : ValidWord arity second)
    (sameSize : first.length = second.length) (sameRank : wordRank arity first = wordRank arity second) :
    first = second := by
  have a := select_word_rank arity first firstValid
  have b := select_word_rank arity second secondValid
  rw [sameSize, sameRank, b] at a
  exact (Option.some.inj a).symm

/-- The recursive callback checks each constructor label and branch before descending. -/
def readWord [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol) :
    Term (Label Symbol) → Option (List Nat)
  | .node .recursion [.node (.choice 0) [.node .pure []]] => some []
  | .node .recursion [.node (.choice (branch + 1)) [.node (.user found) [child]]] =>
      if branch < arity ∧ found = label branch then (readWord arity label child).map (branch :: ·) else none
  | _ => none
termination_by term => sizeOf term

/-- Reading a generated term recovers every branch of its valid word. -/
theorem read_word_term [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (word : List Nat) (valid : ValidWord arity word) : readWord arity label (wordTerm label word) = some word := by
  induction word with
  | nil => simp [wordTerm, readWord]
  | cons branch rest ih =>
      have branchBound : branch < arity := valid branch (by simp)
      have restValid : ValidWord arity rest := fun b member => valid b (by simp [member])
      simp [wordTerm, readWord, branchBound, ih restValid]

/-- Every successful recursive callback has checked the complete member term. -/
theorem read_word_sound [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) (word : List Nat) (read : readWord arity label term = some word) :
    ValidWord arity word ∧ term = wordTerm label word := by
  unfold readWord at read
  split at read
  next => cases read; exact ⟨by simp [ValidWord], rfl⟩
  next branch found child =>
    split at read
    next valid =>
      obtain ⟨rest, foundRest, same⟩ := Option.map_eq_some_iff.mp read
      subst word
      obtain ⟨restValid, childEq⟩ := read_word_sound arity label child rest foundRest
      refine ⟨?_, ?_⟩
      · intro b member
        rcases List.mem_cons.mp member with rfl | member
        · exact valid.1
        · exact restValid b member
      · simp [wordTerm, valid.2, childEq]
    next => cases read
  next => cases read
termination_by sizeOf term

/-- The source callback emits one certified position for this deterministic private grammar. -/
def positions [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) : List Checked :=
  match readWord arity label term with
  | none => []
  | some word => [(⟨word.length, wordRank arity word⟩, true)]

/-- Direct term selection adds the exact private wrappers after class selection. -/
def selectTerm (arity : Nat) (label : Nat → Symbol) (position : Position) : Option (Term (Label Symbol)) :=
  (selectWord arity position.size position.rank).map (wordTerm label)

/-- The actual structural callback and direct decoder have exactly the same positions. -/
theorem positions_exact [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) (position : Position) :
    (position, true) ∈ positions arity label term ↔ selectTerm arity label position = some term := by
  constructor
  · intro member
    unfold positions at member
    cases read : readWord arity label term with
    | none => simp [read] at member
    | some word =>
        have same : position = ⟨word.length, wordRank arity word⟩ := by
          simpa only [read, List.mem_singleton, Prod.mk.injEq, and_true] using member
        obtain ⟨valid, termEq⟩ := read_word_sound arity label term word read
        rw [same, termEq]
        simp [selectTerm, select_word_rank arity word valid]
  · intro selected
    obtain ⟨word, found, same⟩ := Option.map_eq_some_iff.mp selected
    obtain ⟨valid, lengthEq, rankEq⟩ := select_word_sound arity position.size position.rank word found
    rw [← same]
    simp [positions, read_word_term arity label word valid, lengthEq, rankEq]

/-- The literal composed recursion, ordered choice, label, and pay callback. -/
def sourcePositions [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol) :
    Term (Label Symbol) → List Checked
  | .node .recursion [.node (.choice 0) [.node .pure []]] => [(⟨0, 0⟩, true)]
  | .node .recursion [.node (.choice (branch + 1)) [.node (.user found) [child]]] =>
      if branch < arity ∧ found = label branch then
        (sourcePositions arity label child).map fun row =>
          (⟨row.1.size + 1, branch * classCount arity row.1.size + row.1.rank⟩, row.2)
      else []
  | _ => []
termination_by term => sizeOf term

/-- The executable source recurrence computes precisely the structural word position. -/
theorem source_positions_eq [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) : sourcePositions arity label term = positions arity label term := by
  unfold sourcePositions
  split
  next => simp [positions, readWord, wordRank]
  next branch found child =>
    unfold positions
    rw [readWord]
    split
    next valid =>
      rw [source_positions_eq arity label child]
      cases read : readWord arity label child with
      | none => simp [positions, read]
      | some word => simp [positions, read, wordRank, class_count]
    next => rfl
  next => simp_all [positions, readWord]
termination_by sizeOf term

/-- Source leaf views accept exactly one complete recursive member term. -/
def sourceViews [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol) (_view : View) :
    List (Term (Label Symbol)) → List Checked
  | [term] => sourcePositions arity label term
  | _ => []

/-- A private recursion boundary is opaque in each source term view. -/
theorem word_project (label : Nat → Symbol) (word : List Nat) (view : View) :
    project view (wordTerm label word) = [wordTerm label word] := by
  cases word <;> cases view <;>
    simp [wordTerm, project, labelled, spine, SupportTerms.applicationLeftChildren,
      SupportTerms.applicationTermChildren]

/-- Source callbacks are complete with checked symbols in all three term views. -/
theorem source_views_complete [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (word : List Nat) (valid : ValidWord arity word) (view : View) :
    (⟨word.length, wordRank arity word⟩, true) ∈
      sourceViews arity label view (project view (wordTerm label word)) := by
  rw [word_project]
  simp [sourceViews, source_positions_eq, positions, read_word_term arity label word valid]


/-- A certified source candidate replays exactly the requested view in all three projections. -/
theorem source_views_checked [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (view : View) (wanted : List (Term (Label Symbol))) (position : Position)
    (member : (position, true) ∈ sourceViews arity label view wanted) :
    ∃ term, selectTerm arity label position = some term ∧ project view term = wanted := by
  unfold sourceViews at member
  split at member
  next term =>
    rw [source_positions_eq] at member
    have selected := (positions_exact arity label term position).mp member
    obtain ⟨word, found, same⟩ := Option.map_eq_some_iff.mp selected
    exact ⟨term, selected, by rw [← same]; exact word_project label word view⟩
  next => cases member

/-- This recursive family emits at most one candidate for each private term. -/
theorem source_positions_length [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) : (sourcePositions arity label term).length ≤ 1 := by
  rw [source_positions_eq]
  unfold positions
  split <;> simp

/-- The finite prefix of recursive counts includes zero-count classes. -/
def countsThrough (arity bound : Nat) : Sparse.Series Nat :=
  (List.range (bound + 1)).map fun size => (size, arity ^ size)

/-- Every finite prefix is strictly ordered by size. -/
theorem counts_ordered (arity bound : Nat) : Sparse.Ordered (countsThrough arity bound) :=
  List.pairwise_map.mpr (RecursiveSize.range_ordered (bound + 1))

/-- A direct successful decoder supplies the class-bound evidence required by the global rank adapter. -/
theorem select_term_valid (arity : Nat) (label : Nat → Symbol) (position : Position)
    (term : Term (Label Symbol)) (selected : selectTerm arity label position = some term) :
    position.rank < arity ^ position.size := by
  obtain ⟨word, found, _⟩ := Option.map_eq_some_iff.mp selected
  obtain ⟨valid, sizeEq, rankEq⟩ := select_word_sound arity position.size position.rank word found
  simpa [sizeEq, rankEq] using word_rank_bound arity word valid

/-- Valid prefix positions are exactly the bounded sizes and strict class ranks. -/
theorem counts_valid (arity bound : Nat) (position : Position) :
    Valid (countsThrough arity bound) position ↔
      position.size ≤ bound ∧ position.rank < arity ^ position.size := by
  constructor
  · rintro ⟨count, member, bounded⟩
    obtain ⟨size, inRange, same⟩ := List.mem_map.mp member
    obtain ⟨sameSize, sameCount⟩ := Prod.mk.inj same
    have small := List.mem_range.mp inRange
    subst size
    subst count
    exact ⟨by omega, bounded⟩
  · rintro ⟨within, bounded⟩
    exact ⟨arity ^ position.size, List.mem_map.mpr ⟨position.size, List.mem_range.mpr (by omega), rfl⟩, bounded⟩

/-- Size-major decoding reads class counts and one direct class decoder. -/
def selectThrough (arity : Nat) (label : Nat → Symbol) (bound rank : Nat) : Option (Term (Label Symbol)) :=
  (sizeClassOf (countsThrough arity bound) rank).bind (selectTerm arity label)

/-- Bounding the actual source callback filters sizes and retains their original size-major ranks. -/
def rowsThrough [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol) (bound : Nat)
    (term : Term (Label Symbol)) : List StaticCheckedRanks.Checked :=
  ((sourcePositions arity label term).filter fun row => decide (row.1.size ≤ bound)).map
    fun row => (sizeMajorRank (countsThrough arity bound) row.1, row.2)

/-- Each emitted bounded candidate is certified and decodes the complete requested term. -/
theorem rows_through_checked [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (bound : Nat) (term : Term (Label Symbol)) (row : StaticCheckedRanks.Checked)
    (member : row ∈ rowsThrough arity label bound term) :
    row.2 = true ∧ selectThrough arity label bound row.1 = some term := by
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨present, bounded⟩ := List.mem_filter.mp present
  have flag : original.2 = true := by
    rw [source_positions_eq] at present
    unfold positions at present
    split at present
    · cases present
    · exact congrArg Prod.snd (List.mem_singleton.mp present)
  have certified : (original.1, true) ∈ positions arity label term := by
    rw [← source_positions_eq, ← flag]
    exact present
  have selected := (positions_exact arity label term original.1).mp certified
  have valid := (counts_valid arity bound original.1).mpr
    ⟨by simpa using bounded, select_term_valid arity label original.1 term selected⟩
  exact ⟨flag, by simp [selectThrough,
    sizeClassOf_sizeMajorRank _ (counts_ordered arity bound) original.1 valid, selected]⟩

/-- Every successful bounded selection appears as a checked source candidate. -/
theorem rows_through_complete [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (bound rank : Nat) (term : Term (Label Symbol))
    (selected : selectThrough arity label bound rank = some term) :
    (rank, true) ∈ rowsThrough arity label bound term := by
  obtain ⟨position, found, selected⟩ := Option.bind_eq_some_iff.mp selected
  have valid := sizeClassOf_valid _ rank position found
  have within := ((counts_valid arity bound position).mp valid).1
  have present := (positions_exact arity label term position).mpr selected
  rw [← source_positions_eq] at present
  have rankEq := sizeMajorRank_sizeClassOf _ (counts_ordered arity bound) rank position found
  exact List.mem_map.mpr ⟨(position, true), List.mem_filter.mpr ⟨present, by simpa using within⟩,
    by simp [rankEq]⟩

/-- No callback result repeats a rank or violates ascending size-major order. -/
theorem rows_through_ordered [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (bound : Nat) (term : Term (Label Symbol)) :
    ((rowsThrough arity label bound term).map Prod.fst).Pairwise (· < ·) := by
  simp only [rowsThrough, source_positions_eq, positions]
  split
  · simp
  · simp only [List.filter_cons, List.filter_nil]
    split <;> simp

/-- Rank offsets use only the finite count prefix before the requested size. -/
theorem direct_size_major (arity bound : Nat) (position : Position) (within : position.size ≤ bound) :
    sizeMajorRank (countsThrough arity bound) position =
      ((List.range position.size).map (fun size => arity ^ size)).sum + position.rank := by
  unfold sizeMajorRank countsThrough
  rw [countBelow_range _ (bound + 1) position.size (by omega)]


/-- Source sorting leaves this empty or singleton callback unchanged. -/
theorem source_sort_identity [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) (le : Checked → Checked → Bool) :
    (sourcePositions arity label term).mergeSort le = sourcePositions arity label term := by
  simp only [source_positions_eq, positions]
  split <;> simp

/-- The global position uses only coefficients before the requested size. -/
def globalRank (arity : Nat) (position : Position) : Nat :=
  ((List.range position.size).map (fun size => arity ^ size)).sum + position.rank

/-- A positive recursive arity supplies at least one member at every size. -/
theorem prefix_count_lower (arity size : Nat) (positive : 0 < arity) :
    size ≤ ((List.range size).map (fun n => arity ^ n)).sum := by
  induction size with
  | zero => simp
  | succ size ih =>
      have one := Nat.one_le_pow size arity positive
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil]
      omega

/-- A rank's own finite prefix suffices for recursive selection in this positive family. -/
def selectGlobal (arity : Nat) (label : Nat → Symbol) (rank : Nat) : Option (Term (Label Symbol)) :=
  selectThrough arity label rank rank

/-- The source global callback retains each class certificate while adding its size offset. -/
def globalRows [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) : List StaticCheckedRanks.Checked :=
  (sourcePositions arity label term).map fun row => (globalRank arity row.1, row.2)

/-- The positive recursive count table always gives enough ranks in this finite prefix. -/
theorem global_prefix_large (arity rank : Nat) (positive : 0 < arity) :
    rank < ((countsThrough arity rank).map Prod.snd).sum := by
  have lower := prefix_count_lower arity (rank + 1) positive
  simpa only [countsThrough, List.map_map, Function.comp_def] using Nat.lt_of_lt_of_le (by omega : rank < rank + 1) lower

/-- Every nonnegative global rank selects a term without enumerating any class's terms. -/
theorem select_global_total (arity : Nat) (label : Nat → Symbol) (rank : Nat) (positive : 0 < arity) :
    ∃ term, selectGlobal arity label rank = some term := by
  obtain ⟨position, found⟩ := (sizeClassOf_exists_iff (countsThrough arity rank) rank).mpr
    (global_prefix_large arity rank positive)
  have bounded := ((counts_valid arity rank position).mp (sizeClassOf_valid _ _ _ found)).2
  obtain ⟨word, selected⟩ := select_word_total arity position.size position.rank bounded
  exact ⟨wordTerm label word, by simp [selectGlobal, selectThrough, found, selectTerm, selected]⟩

/-- Every global source flag is true and replays the complete requested term. -/
theorem global_checked [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (positive : 0 < arity) (term : Term (Label Symbol)) (row : StaticCheckedRanks.Checked)
    (member : row ∈ globalRows arity label term) :
    row.2 = true ∧ selectGlobal arity label row.1 = some term := by
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have flag : original.2 = true := by
    rw [source_positions_eq] at present
    unfold positions at present
    split at present
    · cases present
    · exact congrArg Prod.snd (List.mem_singleton.mp present)
  have certified : (original.1, true) ∈ positions arity label term := by
    rw [← source_positions_eq, ← flag]
    exact present
  have selected := (positions_exact arity label term original.1).mp certified
  have small : original.1.size ≤ globalRank arity original.1 := by
    have lower := prefix_count_lower arity original.1.size positive
    unfold globalRank
    omega
  have valid := (counts_valid arity (globalRank arity original.1) original.1).mpr
    ⟨small, select_term_valid arity label original.1 term selected⟩
  have rankEq := direct_size_major arity (globalRank arity original.1) original.1 small
  change sizeMajorRank (countsThrough arity (globalRank arity original.1)) original.1 =
    globalRank arity original.1 at rankEq
  have found := sizeClassOf_sizeMajorRank _ (counts_ordered arity _) original.1 valid
  rw [rankEq] at found
  exact ⟨flag, by simp [selectGlobal, selectThrough, found, selected]⟩

/-- Every exact global inverse is emitted with a checked certificate. -/
theorem global_complete [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (rank : Nat) (term : Term (Label Symbol)) (selected : selectGlobal arity label rank = some term) :
    (rank, true) ∈ globalRows arity label term := by
  obtain ⟨position, found, selected⟩ := Option.bind_eq_some_iff.mp selected
  have valid := sizeClassOf_valid _ rank position found
  have within := ((counts_valid arity rank position).mp valid).1
  have present := (positions_exact arity label term position).mpr selected
  rw [← source_positions_eq] at present
  have rankEq := sizeMajorRank_sizeClassOf _ (counts_ordered arity rank) rank position found
  rw [direct_size_major arity rank position within] at rankEq
  change globalRank arity position = rank at rankEq
  exact List.mem_map.mpr ⟨(position, true), present, by simp [rankEq]⟩

/-- Actual global callbacks have strict order and no repeated ranks. -/
theorem global_ordered [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) : ((globalRows arity label term).map Prod.fst).Pairwise (· < ·) := by
  simp only [globalRows, source_positions_eq, positions]
  split <;> simp

/-- Signed public replay uses the source negative-rank rejection. -/
def publicDecode (arity : Nat) (label : Nat → Symbol) : Int → Except Unit (Term (Label Symbol)) :=
  CompositeCheckedRanks.replay (selectGlobal arity label)

/-- The public recursive source has a concrete available term callback. -/
def publicSource [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol) :
    CheckedRankQueries.Source Unit (Term (Label Symbol)) :=
  .recursive (.ok (some fun term => CompositeCheckedRanks.publicCandidates (globalRows arity label term)))

/-- The recursive producer discharges the public shortcut's complete checked-symbol obligation. -/
theorem public_checked [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol) (positive : 0 < arity)
    (term : Term (Label Symbol)) :
    CheckedRankQueries.CheckedSound (publicDecode arity label) term
      (CompositeCheckedRanks.publicCandidates (globalRows arity label term)) := by
  apply CompositeCheckedRanks.certified_public
  intro row member _
  exact (global_checked arity label positive term row member).2

/-- Public completeness follows from the recursive callback, with no callback assumption. -/
theorem public_complete [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) :
    CheckedRankQueries.Complete (publicDecode arity label) term
      (CompositeCheckedRanks.publicCandidates (globalRows arity label term)) := by
  intro rank selected
  have nonnegative : ¬rank < 0 := by
    intro negative
    simp [publicDecode, CompositeCheckedRanks.replay, negative] at selected
  have decoded : selectGlobal arity label rank.toNat = some term := by
    cases found : selectGlobal arity label rank.toNat <;>
      simp_all [publicDecode, CompositeCheckedRanks.replay]
  have member := global_complete arity label rank.toNat term decoded
  refine ⟨⟨rank.toNat, true⟩, List.mem_map.mpr ⟨(rank.toNat, true), member, rfl⟩, ?_⟩
  dsimp
  omega

/-- Signed public candidate order follows from the concrete recursive callback. -/
theorem public_ordered [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (term : Term (Label Symbol)) :
    ((CompositeCheckedRanks.publicCandidates (globalRows arity label term)).map CheckedRankQueries.Candidate.rank).Pairwise (· ≤ ·) := by
  have order := global_ordered arity label term
  have castOrder := order.map (fun rank : Nat => (rank : Int)) (fun a b before => by omega : ∀ a b : Nat, a < b → (a : Int) ≤ b)
  simpa only [CompositeCheckedRanks.publicCandidates, List.map_map, Function.comp_def] using castOrder

/-- Public recursive inversion returns exactly the least correct signed replay rank. -/
theorem public_rank_exact [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol) (positive : 0 < arity)
    (term : Term (Label Symbol)) (rank : Int) :
    CheckedRankQueries.rankOf (publicDecode arity label) (publicSource arity label) term = .ok rank ↔
      publicDecode arity label rank = .ok term ∧
        ∀ other, publicDecode arity label other = .ok term → rank ≤ other :=
  CheckedRankQueries.rankOf_exact _ _ _ _ rfl
    (public_checked arity label positive term) (public_complete arity label term)
    (public_ordered arity label term) rank


/-- Finite recursive selection succeeds on exactly the contiguous bounded rank interval. -/
theorem bounded_rank_interval (arity : Nat) (label : Nat → Symbol) (bound rank : Nat) :
    (∃ term, selectThrough arity label bound rank = some term) ↔
      rank < ((countsThrough arity bound).map Prod.snd).sum := by
  constructor
  · rintro ⟨term, selected⟩
    obtain ⟨position, found, _⟩ := Option.bind_eq_some_iff.mp selected
    exact (sizeClassOf_exists_iff _ rank).mp ⟨position, found⟩
  · intro within
    obtain ⟨position, found⟩ := (sizeClassOf_exists_iff (countsThrough arity bound) rank).mpr within
    have valid := ((counts_valid arity bound position).mp (sizeClassOf_valid _ _ _ found)).2
    obtain ⟨word, selected⟩ := select_word_total arity position.size position.rank valid
    exact ⟨wordTerm label word, by simp [selectThrough, found, selectTerm, selected]⟩

/-- Distinct bounded ranks have distinct complete private terms. -/
theorem bounded_rank_unique [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (bound first second : Nat) (term : Term (Label Symbol))
    (a : selectThrough arity label bound first = some term)
    (b : selectThrough arity label bound second = some term) : first = second := by
  have ma := rows_through_complete arity label bound first term a
  have mb := rows_through_complete arity label bound second term b
  simp only [rowsThrough, source_positions_eq, positions] at ma mb
  cases read : readWord arity label term with
  | none => simp [read] at ma
  | some word =>
      simp only [read, List.filter_cons, List.filter_nil] at ma mb
      split at ma
      next inside => simp [inside] at ma mb; omega
      next outside => simp_all

/-- Distinct global ranks have distinct complete private terms. -/
theorem global_rank_unique [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (first second : Nat) (term : Term (Label Symbol))
    (a : selectGlobal arity label first = some term)
    (b : selectGlobal arity label second = some term) : first = second := by
  have ma := global_complete arity label first term a
  have mb := global_complete arity label second term b
  simp only [globalRows, source_positions_eq, positions] at ma mb
  cases read : readWord arity label term with
  | none => simp [read] at ma
  | some word => simp [read] at ma mb; omega

/-- The bounded indexed language contains all and only valid words up to its size limit. -/
theorem bounded_language_exact [DecidableEq Symbol] (arity : Nat) (label : Nat → Symbol)
    (bound : Nat) (term : Term (Label Symbol)) :
    (∃ rank, selectThrough arity label bound rank = some term) ↔
      ∃ word, ValidWord arity word ∧ word.length ≤ bound ∧ term = wordTerm label word := by
  constructor
  · rintro ⟨rank, selected⟩
    obtain ⟨position, found, selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨word, wordFound, same⟩ := Option.map_eq_some_iff.mp selected
    obtain ⟨valid, sizeEq, _⟩ := select_word_sound arity position.size position.rank word wordFound
    have within := ((counts_valid arity bound position).mp (sizeClassOf_valid _ _ _ found)).1
    exact ⟨word, valid, by omega, same.symm⟩
  · rintro ⟨word, valid, within, rfl⟩
    let position : Position := ⟨word.length, wordRank arity word⟩
    have classValid := (counts_valid arity bound position).mpr ⟨within, word_rank_bound arity word valid⟩
    refine ⟨sizeMajorRank (countsThrough arity bound) position, ?_⟩
    simp [selectThrough, sizeClassOf_sizeMajorRank _ (counts_ordered arity bound) position classValid,
      selectTerm, position, select_word_rank arity word valid]

/-- Two unary alternatives give the exact class sizes and direct callback rank. -/
theorem binary_example :
    classCount 2 8 = 256 ∧
    sourcePositions 2 (fun n => n) (wordTerm (fun n => n) [1, 0, 1]) = [(⟨3, 5⟩, true)] ∧
    globalRows 2 (fun n => n) (wordTerm (fun n => n) [1, 0, 1]) = [(12, true)] ∧
    selectGlobal 2 (fun n => n) 12 = some (wordTerm (fun n => n) [1, 0, 1]) := by decide +kernel

/-- Repeated user labels do not merge the source's distinct private choice members. -/
theorem repeated_label_example :
    globalRows 2 (fun _ => 7) (wordTerm (fun _ => 7) [0]) = [(1, true)] ∧
    globalRows 2 (fun _ => 7) (wordTerm (fun _ => 7) [1]) = [(2, true)] := by decide +kernel


end MicroCFTA.RecursiveCheckedRanks
