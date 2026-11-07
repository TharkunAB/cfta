import MicroCFTA.SourceSizedDeterminizationOrderedStep

/-!
# Generated arity and the source zip target

The source groups transitions by symbol and arity before it generates tuples.
Its target predicate uses `and (zipWith Set.member children keys)`.
Generated tuples have the group's arity. The zip therefore checks every
child position. A symbol can occur in several arity groups.

The target below reads a source set as an ascending list. Its equality
with the kernel target does not identify a native container representation.
-/
namespace MicroCFTA.SourceSizedDeterminizationZipTarget
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationFrontier Std

/-- Execute the source zip of child membership tests, followed by conjunction. -/
def zipMatches {State : Type} [DecidableEq State]
    (children : List State) (keys : List (List State)) : Bool :=
  (List.zipWith (fun state key => decide (state ∈ key)) children keys).all id

/-- Equal lengths make the source zip test equal to the full positional test. -/
theorem zipMatches_eq {State : Type} [DecidableEq State]
    (children : List State) (keys : List (List State))
    (arity : children.length = keys.length) :
    zipMatches children keys = childrenMatch children keys := by
  induction children generalizing keys with
  | nil =>
      cases keys with
      | nil => rfl
      | cons key keys => simp at arity
  | cons child children ih =>
      cases keys with
      | nil => simp at arity
      | cons key keys =>
          change (decide (child ∈ key) && zipMatches children keys) =
            (decide (child ∈ key) && childrenMatch children keys)
          rw [ih keys (by simpa using arity)]

/-- The equal-length source zip succeeds exactly for pointwise membership. -/
theorem zipMatches_iff {State : Type} [DecidableEq State]
    (children : List State) (keys : List (List State))
    (arity : children.length = keys.length) :
    zipMatches children keys = true ↔ All₂ (fun state key => state ∈ key) children keys := by
  rw [zipMatches_eq children keys arity, childrenMatch_iff]

/-- Read one token bucket in original owner and transition order. -/
def members {State Symbol : Type} [DecidableEq Symbol]
    (states : List State) (rows : Automaton State Symbol) (wanted : Symbol × Nat) :
    List (State × Edge State Symbol) :=
  states.flatMap fun state =>
    ((rows state).filter fun edge => decide (SourceSizedDeterminizationStep.token edge = wanted)).map
      fun edge => (state, edge)

/-- A token bucket retains exactly the original transitions with that full token. -/
theorem mem_members {State Symbol : Type} [DecidableEq Symbol]
    (states : List State) (rows : Automaton State Symbol) (wanted : Symbol × Nat)
    (state : State) (edge : Edge State Symbol) :
    (state, edge) ∈ members states rows wanted ↔
      state ∈ states ∧ edge ∈ rows state ∧ SourceSizedDeterminizationStep.token edge = wanted := by
  simp only [members, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨owner, present, transition, ⟨stored, selected⟩, same⟩
    have ownerEq : owner = state := congrArg Prod.fst same
    have edgeEq : transition = edge := congrArg Prod.snd same
    subst owner
    subst transition
    exact ⟨present, stored, selected⟩
  · rintro ⟨present, stored, selected⟩
    exact ⟨state, present, edge, ⟨stored, selected⟩, rfl⟩

/-- Every tuple in a source tuple set has the token's arity. -/
theorem tupleSet_arity {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
    [Ord State] (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) (keys : List (List State))
    (member : keys ∈ SourceSizedDeterminizationOrderedStep.tupleSet states rows fresh holding known wanted) :
    keys.length = wanted.2 := by
  have raw : keys ∈ (SourceSizedDeterminizationStep.seeds states rows wanted).flatMap
      (tuples fresh holding known) := (CanonicalClasses.mem_sortedSet _ _).mp member
  obtain ⟨children, seeded, generated⟩ := List.mem_flatMap.mp raw
  unfold SourceSizedDeterminizationStep.seeds at seeded
  obtain ⟨state, _, mapped⟩ := List.mem_flatMap.mp seeded
  obtain ⟨edge, filtered, rfl⟩ := List.mem_map.mp mapped
  have tokenEq : SourceSizedDeterminizationStep.token edge = wanted :=
    of_decide_eq_true (List.mem_filter.mp filtered).2
  have lengths := ((mem_tuples fresh holding known edge.children keys).mp generated).1.length_eq
  exact lengths.symm.trans (congrArg Prod.snd tokenEq)

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

/-- Retain the owners that pass the source zip predicate in one token bucket. -/
def selectedOwners (states : List State) (rows : Automaton State Symbol)
    (wanted : Symbol × Nat) (keys : List (List State)) : List State :=
  ((members states rows wanted).filter fun entry => zipMatches entry.2.children keys).map Prod.fst

/-- Equal token arity gives exactly the kernel target's owner membership. -/
theorem mem_selectedOwners (states : List State) (rows : Automaton State Symbol)
    (wanted : Symbol × Nat) (keys : List (List State)) (arity : keys.length = wanted.2)
    (state : State) :
    state ∈ selectedOwners states rows wanted keys ↔ state ∈ target states rows wanted.1 keys := by
  rw [mem_target]
  constructor
  · intro member
    obtain ⟨entry, selected, same⟩ := List.mem_map.mp member
    rcases entry with ⟨owner, edge⟩
    change owner = state at same
    subst owner
    obtain ⟨stored, passed⟩ := List.mem_filter.mp selected
    obtain ⟨present, transition, tokenEq⟩ := (mem_members states rows wanted state edge).mp stored
    have lengths : edge.children.length = keys.length :=
      (congrArg Prod.snd tokenEq).trans arity.symm
    exact ⟨present, edge, transition, congrArg Prod.fst tokenEq,
      (zipMatches_iff edge.children keys lengths).mp passed⟩
  · rintro ⟨present, edge, stored, label, related⟩
    have lengths := related.length_eq
    have tokenEq : SourceSizedDeterminizationStep.token edge = wanted :=
      Prod.ext label (lengths.trans arity)
    apply List.mem_map.mpr
    refine ⟨(state, edge), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (mem_members states rows wanted state edge).mpr ⟨present, stored, tokenEq⟩
    · exact (zipMatches_iff edge.children keys lengths).mpr related

/-- Read the target produced by the source `Set.fromList` as an ascending list. -/
def sourceTarget [Ord State] (states : List State) (rows : Automaton State Symbol)
    (wanted : Symbol × Nat) (keys : List (List State)) : List State :=
  CanonicalClasses.sortedSet (selectedOwners states rows wanted keys)

/-- At the token's arity, source target readback is the canonical kernel target. -/
theorem sourceTarget_eq [Ord State] [TransOrd State] [LawfulEqOrd State]
    (states : List State) (rows : Automaton State Symbol)
    (wanted : Symbol × Nat) (keys : List (List State)) (arity : keys.length = wanted.2) :
    sourceTarget states rows wanted keys = CanonicalClasses.sortedSet (target states rows wanted.1 keys) := by
  apply CanonicalClasses.sortedSet_ext
  intro state
  exact mem_selectedOwners states rows wanted keys arity state

/-- Every emitted tuple makes the literal source zip target equal to the canonical target. -/
theorem generated_target_eq [Ord State] [TransOrd State] [LawfulEqOrd State]
    (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) (keys : List (List State))
    (member : keys ∈ SourceSizedDeterminizationOrderedStep.tupleSet states rows fresh holding known wanted) :
    sourceTarget states rows wanted keys = CanonicalClasses.sortedSet (target states rows wanted.1 keys) :=
  sourceTarget_eq states rows wanted keys (tupleSet_arity states rows fresh holding known wanted keys member)

end MicroCFTA.SourceSizedDeterminizationZipTarget
