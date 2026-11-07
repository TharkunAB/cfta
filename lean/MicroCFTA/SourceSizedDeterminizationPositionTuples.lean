import MicroCFTA.SourceSizedDeterminizationOrderedStep

/-!
# Literal first-fresh-position tuples

The source zips all prefixes with all suffixes. A nonempty suffix gives
the pivot child. Earlier children use older keys. The pivot uses a fresh
key. Later children use all holders. The final empty suffix emits nothing.

Lean's list library has no `inits` or `tails` functions. The definitions
below use their source recurrences. Positions are the literal zip.
Only membership is compared with the recursive frontier. Its intermediate
list order can differ. Sorted set readback removes that order difference.
-/
namespace MicroCFTA.SourceSizedDeterminizationPositionTuples
open Language Std
attribute [local instance] lexOrd

/-- Read all prefixes, from the empty prefix to the complete input. -/
def inits {State : Type} : List State → List (List State)
  | [] => [[]]
  | first :: rest => [] :: (inits rest).map (first :: ·)

/-- Read all suffixes, from the complete input to the empty suffix. -/
def tails {State : Type} : List State → List (List State)
  | [] => [[]]
  | first :: rest => (first :: rest) :: tails rest

/-- The source enumerates positions by zipping prefixes with suffixes. -/
def positions {State : Type} (states : List State) : List (List State × List State) :=
  (inits states).zip (tails states)

/-- A leading child shifts each later prefix and preserves each later suffix. -/
theorem positions_cons {State : Type} (first : State) (rest : List State) :
    positions (first :: rest) = ([], first :: rest) ::
      (positions rest).map (fun position => (first :: position.1, position.2)) := by
  simp only [positions, inits, tails, List.zip_cons_cons, List.zip_map_left]
  congr 1

/-- Each zipped pair is exactly one split of the original child list. -/
theorem mem_positions {State : Type} (states earlier later : List State) :
    (earlier, later) ∈ positions states ↔ states = earlier ++ later := by
  induction states generalizing earlier later with
  | nil => cases earlier <;> cases later <;> simp [positions, inits, tails]
  | cons first rest ih =>
    rw [positions_cons]
    constructor
    · intro member
      rcases List.mem_cons.mp member with same | tail
      · have prefixEq : earlier = [] := congrArg Prod.fst same
        have suffixEq : later = first :: rest := congrArg Prod.snd same
        rw [prefixEq, suffixEq]
        rfl
      · obtain ⟨position, present, same⟩ := List.mem_map.mp tail
        have prefixEq : first :: position.1 = earlier := congrArg Prod.fst same
        have suffixEq : position.2 = later := congrArg Prod.snd same
        rw [← prefixEq, ← suffixEq]
        exact congrArg (List.cons first) ((ih position.1 position.2).mp present)
    · intro split
      cases earlier with
      | nil =>
        simp only [List.nil_append] at split
        subst later
        exact List.mem_cons_self
      | cons owner earlier =>
        have pieces : first = owner ∧ rest = earlier ++ later := by
          simpa only [List.cons_append, List.cons.injEq] using split
        have ownerEq := pieces.1
        subst owner
        exact List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨(earlier, later), (ih earlier later).mpr pieces.2, rfl⟩)

variable {State Key : Type} [DecidableEq Key]

/-- Emit one source position, with the same prefix, pivot, and suffix loop order. -/
def block (fresh : List Key) (holding : State → List Key)
    (position : List State × List State) : List (List Key) :=
  match position.2 with
  | [] => []
  | pivot :: later =>
    (products (fun state => (holding state).filter fun key => decide (key ∉ fresh)) position.1).flatMap
      fun earlierKeys => ((holding pivot).filter fun key => decide (key ∈ fresh)).flatMap
        fun chosen => (products holding later).map fun laterKeys => earlierKeys ++ (chosen :: laterKeys)

/-- Concatenate the literal source position blocks before tuple-set conversion. -/
def delta (fresh : List Key) (holding : State → List Key) (states : List State) : List (List Key) :=
  (positions states).flatMap (block fresh holding)

private theorem append_related {A B : Type} {relation : A → B → Prop}
    {leftA rightA : List A} {leftB rightB : List B}
    (first : All₂ relation leftA leftB) (second : All₂ relation rightA rightB) :
    All₂ relation (leftA ++ rightA) (leftB ++ rightB) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem first_fresh (fresh : List Key) (holding : State → List Key)
    {states : List State} {keys : List Key}
    (related : All₂ (fun state key => key ∈ holding state) states keys)
    (recent : ∃ key ∈ keys, key ∈ fresh) :
    ∃ earlier pivot later earlierKeys chosen laterKeys,
      states = earlier ++ (pivot :: later) ∧
      keys = earlierKeys ++ (chosen :: laterKeys) ∧
      earlierKeys ∈ products (fun state => (holding state).filter fun key => decide (key ∉ fresh)) earlier ∧
      chosen ∈ holding pivot ∧ chosen ∈ fresh ∧ laterKeys ∈ products holding later := by
  revert recent
  induction related with
  | nil =>
    rintro ⟨key, impossible, _⟩
    cases impossible
  | @cons state key states keys stored related ih =>
    intro recent
    by_cases newKey : key ∈ fresh
    · exact ⟨[], state, states, [], key, keys, rfl, rfl,
        by simp [products], stored, newKey, (mem_products holding states keys).mpr related⟩
    · have tailRecent : ∃ next ∈ keys, next ∈ fresh := by
        obtain ⟨next, present, isFresh⟩ := recent
        rcases List.mem_cons.mp present with same | tail
        · exact False.elim (newKey (same ▸ isFresh))
        · exact ⟨next, tail, isFresh⟩
      obtain ⟨earlier, pivot, later, earlierKeys, chosen, laterKeys,
        split, keysEq, prefixSelected, storedChosen, freshChosen, suffixSelected⟩ := ih tailRecent
      refine ⟨state :: earlier, pivot, later, key :: earlierKeys, chosen, laterKeys,
        ?_, ?_, ?_, storedChosen, freshChosen, suffixSelected⟩
      · exact congrArg (List.cons state) split
      · exact congrArg (List.cons key) keysEq
      · apply (mem_products _ _ _).mpr
        exact .cons (List.mem_filter.mpr ⟨stored, decide_eq_true newKey⟩)
          ((mem_products _ _ _).mp prefixSelected)

/-- A literal positional tuple is pointwise valid and contains a fresh key. -/
theorem mem_delta (fresh : List Key) (holding : State → List Key)
    (states : List State) (keys : List Key) :
    keys ∈ delta fresh holding states ↔
      All₂ (fun state key => key ∈ holding state) states keys ∧
        ∃ key ∈ keys, key ∈ fresh := by
  constructor
  · intro member
    obtain ⟨position, present, generated⟩ := List.mem_flatMap.mp member
    rcases position with ⟨earlier, suffix⟩
    cases suffix with
    | nil => cases generated
    | cons pivot later =>
      obtain ⟨earlierKeys, prefixSelected, chosen, selected, laterKeys, suffixSelected, same⟩ :=
        (by simpa only [block, List.mem_flatMap, List.mem_map] using generated :
          ∃ earlierKeys ∈ products
            (fun state => (holding state).filter fun key => decide (key ∉ fresh)) earlier,
            ∃ chosen ∈ (holding pivot).filter (fun key => decide (key ∈ fresh)),
              ∃ laterKeys ∈ products holding later, earlierKeys ++ (chosen :: laterKeys) = keys)
      have split := (mem_positions states earlier (pivot :: later)).mp present
      subst states
      subst keys
      have prefixRelated := (mem_products _ _ _).mp prefixSelected
      have suffixRelated := (mem_products holding later laterKeys).mp suffixSelected
      have chosenFacts := List.mem_filter.mp selected
      refine ⟨append_related
        (prefixRelated.imp (fun _ _ stored => (List.mem_filter.mp stored).1))
        (.cons chosenFacts.1 suffixRelated), ?_⟩
      exact ⟨chosen, List.mem_append.mpr (Or.inr List.mem_cons_self),
        of_decide_eq_true chosenFacts.2⟩
  · rintro ⟨related, recent⟩
    obtain ⟨earlier, pivot, later, earlierKeys, chosen, laterKeys,
      split, keysEq, prefixSelected, storedChosen, freshChosen, suffixSelected⟩ :=
      first_fresh fresh holding related recent
    apply List.mem_flatMap.mpr
    refine ⟨(earlier, pivot :: later), (mem_positions states earlier (pivot :: later)).mpr split, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨earlierKeys, prefixSelected, ?_⟩
    apply List.mem_flatMap.mpr
    exact ⟨chosen, List.mem_filter.mpr ⟨storedChosen, decide_eq_true freshChosen⟩,
      List.mem_map.mpr ⟨laterKeys, suffixSelected, keysEq.symm⟩⟩

/-- The source treats leaf tuples separately from its position comprehension. -/
def tuples (fresh : List Key) (holding : State → List Key) (known : List Key) :
    List State → List (List Key)
  | [] => if known = [] then [[]] else []
  | state :: states => delta fresh holding (state :: states)

/-- Positional enumeration and the recursive frontier have identical tuple membership. -/
theorem tuples_mem_iff (fresh : List Key) (holding : State → List Key) (known : List Key)
    (states : List State) (keys : List Key) :
    keys ∈ tuples fresh holding known states ↔
      keys ∈ SourceSizedDeterminizationFrontier.tuples fresh holding known states := by
  cases states with
  | nil => rfl
  | cons state states =>
    exact (mem_delta fresh holding (state :: states) keys).trans
      (SourceSizedDeterminizationFrontier.mem_delta fresh holding (state :: states) keys).symm

/-- Tuple membership includes the exact initial-leaf and first-fresh alternatives. -/
theorem mem_tuples (fresh : List Key) (holding : State → List Key) (known : List Key)
    (states : List State) (keys : List Key) :
    keys ∈ tuples fresh holding known states ↔
      All₂ (fun state key => key ∈ holding state) states keys ∧
        ((states = [] ∧ known = []) ∨ ∃ key ∈ keys, key ∈ fresh) :=
  (tuples_mem_iff fresh holding known states keys).trans
    (SourceSizedDeterminizationFrontier.mem_tuples fresh holding known states keys)

/-- Canonical readback removes the intermediate enumeration-order difference. -/
theorem sorted_tuples_eq [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (fresh : List Key) (holding : State → List Key) (known : List Key) (states : List State) :
    CanonicalClasses.sortedSet (tuples fresh holding known states) =
      CanonicalClasses.sortedSet (SourceSizedDeterminizationFrontier.tuples fresh holding known states) := by
  apply CanonicalClasses.sortedSet_ext
  intro keys
  exact tuples_mem_iff fresh holding known states keys

/-- Sorting the concatenated source seeds gives the existing complete token tuple set. -/
theorem sorted_seeds_eq [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (fresh : List Key) (holding : State → List Key) (known : List Key) (seeds : List (List State)) :
    CanonicalClasses.sortedSet (seeds.flatMap (tuples fresh holding known)) =
      CanonicalClasses.sortedSet (seeds.flatMap (SourceSizedDeterminizationFrontier.tuples fresh holding known)) := by
  apply CanonicalClasses.sortedSet_ext
  intro keys
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨seed, present, generated⟩
    exact ⟨seed, present, (tuples_mem_iff fresh holding known seed keys).mp generated⟩
  · rintro ⟨seed, present, generated⟩
    exact ⟨seed, present, (tuples_mem_iff fresh holding known seed keys).mpr generated⟩

end MicroCFTA.SourceSizedDeterminizationPositionTuples
