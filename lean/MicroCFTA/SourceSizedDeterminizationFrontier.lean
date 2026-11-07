import MicroCFTA.Language

/-!
# Tuples with a first fresh child subset

The source is the semi-naive `tuples` worker in
`Gen.Internal.Table.deterministicRows`. The source sorts and removes repeated
tuples after it combines the transition seeds. This recursive list view has
the same tuple membership. It does not specify the final row order.

A nonempty tuple has a first fresh position. Positions before it use older
keys. Positions after it use any known key. The empty tuple occurs only in
the initial round, when the known set is empty.
-/
namespace MicroCFTA.SourceSizedDeterminizationFrontier
open Language

variable {State Key : Type} [DecidableEq Key]

/-- Generate tuples by their first fresh position. -/
def delta (fresh : List Key) (holding : State → List Key) : List State → List (List Key)
  | [] => []
  | state :: states =>
      ((holding state).filter fun key => decide (key ∈ fresh)).flatMap
        (fun key => (products holding states).map (key :: ·)) ++
      ((holding state).filter fun key => decide (key ∉ fresh)).flatMap
        (fun key => (delta fresh holding states).map (key :: ·))

/-- Delta tuples are exactly the pointwise choices with at least one fresh key. -/
theorem mem_delta (fresh : List Key) (holding : State → List Key)
    (states : List State) (keys : List Key) :
    keys ∈ delta fresh holding states ↔
      All₂ (fun state key => key ∈ holding state) states keys ∧
        ∃ key ∈ keys, key ∈ fresh := by
  induction states generalizing keys with
  | nil =>
      constructor
      · simp [delta]
      · rintro ⟨related, key, member, _⟩
        cases related
        cases member
  | cons state states ih =>
      constructor
      · intro found
        rcases List.mem_append.mp found with firstFresh | olderFirst
        · obtain ⟨key, selected, present⟩ := List.mem_flatMap.mp firstFresh
          obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp present
          have selected := List.mem_filter.mp selected
          exact ⟨.cons selected.1 ((mem_products holding states tail).mp tailMember),
            key, by simp, of_decide_eq_true selected.2⟩
        · obtain ⟨key, selected, present⟩ := List.mem_flatMap.mp olderFirst
          obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp present
          obtain ⟨related, freshKey, inTail, isFresh⟩ := (ih tail).mp tailMember
          exact ⟨.cons (List.mem_filter.mp selected).1 related,
            freshKey, List.mem_cons_of_mem key inTail, isFresh⟩
      · rintro ⟨related, freshKey, inside, isFresh⟩
        cases related with
        | @cons _ key _ keys member related =>
          by_cases newKey : key ∈ fresh
          · apply List.mem_append_left
            apply List.mem_flatMap.mpr
            exact ⟨key, List.mem_filter.mpr ⟨member, decide_eq_true newKey⟩,
              List.mem_map.mpr ⟨keys, (mem_products holding states keys).mpr related, rfl⟩⟩
          · have freshTail : ∃ next ∈ keys, next ∈ fresh := by
              rcases List.mem_cons.mp inside with same | tail
              · exact False.elim (newKey (same ▸ isFresh))
              · exact ⟨freshKey, tail, isFresh⟩
            apply List.mem_append_right
            apply List.mem_flatMap.mpr
            exact ⟨key, List.mem_filter.mpr ⟨member, decide_eq_true newKey⟩,
              List.mem_map.mpr ⟨keys, (ih keys).mpr ⟨related, freshTail⟩, rfl⟩⟩

/-- The empty child tuple is emitted only before discovery has found a key. -/
def tuples (fresh : List Key) (holding : State → List Key) (known : List Key) :
    List State → List (List Key)
  | [] => if known = [] then [[]] else []
  | state :: states => delta fresh holding (state :: states)

/-- Every source tuple is initial and empty, or contains a fresh child subset. -/
theorem mem_tuples (fresh : List Key) (holding : State → List Key) (known : List Key)
    (states : List State) (keys : List Key) :
    keys ∈ tuples fresh holding known states ↔
      All₂ (fun state key => key ∈ holding state) states keys ∧
        ((states = [] ∧ known = []) ∨ ∃ key ∈ keys, key ∈ fresh) := by
  cases states with
  | nil =>
      by_cases empty : known = []
      · constructor
        · intro member
          have same : keys = [] := by simpa only [tuples, empty, ↓reduceIte, List.mem_singleton] using member
          subst keys
          exact ⟨.nil, Or.inl ⟨rfl, empty⟩⟩
        · rintro ⟨related, _⟩
          cases related
          simp [tuples, empty]
      · constructor
        · simp [tuples, empty]
        · rintro ⟨related, initial | ⟨key, member, _⟩⟩
          · exact False.elim (empty initial.2)
          · cases related
            cases member
  | cons state states =>
      rw [tuples, mem_delta]
      constructor
      · rintro ⟨related, fresh⟩
        exact ⟨related, Or.inr fresh⟩
      · rintro ⟨related, initial | fresh⟩
        · cases initial.1
        · exact ⟨related, fresh⟩

/-- The initial round generates exactly the leaf child tuple. -/
theorem tuples_initial (states : List State) :
    tuples ([] : List Key) (fun (_ : State) => []) [] states =
      if states = [] then [[]] else [] := by
  cases states <;> simp [tuples, delta]

/-- Once discovery has started, a tuple made only of old keys cannot be emitted again. -/
theorem old_tuple_excluded (fresh : List Key) (holding : State → List Key) (known : List Key)
    (started : known ≠ []) (states : List State) (keys : List Key)
    (older : ∀ key ∈ keys, key ∉ fresh) : keys ∉ tuples fresh holding known states := by
  intro member
  rcases ((mem_tuples fresh holding known states keys).mp member).2 with initial | freshKey
  · exact started initial.2
  · obtain ⟨key, present, isFresh⟩ := freshKey
    exact older key present isFresh

end MicroCFTA.SourceSizedDeterminizationFrontier
