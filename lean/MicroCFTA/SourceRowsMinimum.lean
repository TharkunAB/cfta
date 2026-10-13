import MicroCFTA.MinimumSize

/-!
# Actual minimum-size convergence over a finite row map

Only listed keys can change in a sweep. The state type can be infinite, as
InternedState is. Missing rows and absent minimum entries remain separate.
The recurrence reads only ordered child states and ignores constraints.
-/

namespace MicroCFTA.SourceRowsMinimum

open Language RecursiveSize MinimumSize

/-- Every nonempty row is stored under a visited finite map key. -/
def Supported (automaton : Automaton State Symbol) (keys : List State) : Prop :=
  ∀ state edge, edge ∈ automaton state → state ∈ keys

/-- A sweep cannot change an entry outside its actual finite map domain. -/
theorem sweep_outside [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State)
    (known : State → Option Nat) (state : State) (outside : state ∉ keys) :
    sweep automaton keys known state = known state := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      have different : state ≠ key := fun same => outside (by simp [same])
      have absent : state ∉ keys := fun present => outside (by simp [present])
      simpa [sweep, relax, different] using ih absent

/-- Equality on visited keys suffices because every other entry is unchanged. -/
theorem same_sweep_iff [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State)
    (known : State → Option Nat) :
    sameTable keys (sweep automaton keys known) known = true ↔ sweep automaton keys known = known := by
  constructor
  · intro same
    funext state
    by_cases present : state ∈ keys
    · exact of_decide_eq_true (List.all_eq_true.mp same state present)
    · exact sweep_outside automaton keys known state present
  · intro same
    simp [sameTable, same]

/-- Each unequal source sweep strictly decreases the same finite two-part measure. -/
theorem sweep_decreases [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State)
    (known : State → Option Nat) (different : sweep automaton keys known ≠ known) :
    missing keys (sweep automaton keys known) < missing keys known ∨
      (missing keys (sweep automaton keys known) = missing keys known ∧
        total keys (sweep automaton keys known) < total keys known) := by
  have measure := measure_refines keys known (sweep automaton keys known) (sweep_refines automaton keys known)
  by_cases sameMissing : missing keys (sweep automaton keys known) = missing keys known
  · right
    refine ⟨sameMissing, ?_⟩
    obtain ⟨weak, equal⟩ := measure.2 sameMissing
    have unequal : total keys (sweep automaton keys known) ≠ total keys known := by
      intro sameTotal
      apply different
      funext state
      by_cases present : state ∈ keys
      · exact (equal sameTotal state present).symm
      · exact sweep_outside automaton keys known state present
    omega
  · exact Or.inl (by omega)

/-- Repeat the actual right-fold sweep until the finite map is unchanged. -/
def converge [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State)
    (known : State → Option Nat) : State → Option Nat :=
  let next := sweep automaton keys known
  if _stable : sameTable keys next known = true then known else converge automaton keys next
termination_by (missing keys known, total keys known)
decreasing_by
  have different : sweep automaton keys known ≠ known := by
    intro equal
    exact _stable ((same_sweep_iff automaton keys known).mpr equal)
  rcases sweep_decreases automaton keys known different with fewer | ⟨same, smaller⟩
  · exact Prod.Lex.left _ _ fewer
  · rw [same]
    exact Prod.Lex.right _ smaller

/-- Starting from Map.empty computes the source minimum table. -/
def minimumSizes [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State) : State → Option Nat :=
  converge automaton keys (fun _ => none)

/-- Source convergence always returns a stable table. -/
theorem converge_fixed [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State)
    (known : State → Option Nat) : sweep automaton keys (converge automaton keys known) = converge automaton keys known := by
  induction known using converge.induct automaton keys with
  | case1 known next stable =>
      dsimp only [next] at stable
      rw [converge.eq_def]
      simp only [dite_eq_left stable]
      exact (same_sweep_iff automaton keys known).mp stable
  | case2 known next unstable ih =>
      dsimp only [next] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih

/-- The complete source computation is reached after finitely many ordinary sweeps. -/
theorem converge_reached [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State)
    (known : State → Option Nat) : ∃ fuel, sweeps automaton keys fuel known = converge automaton keys known := by
  induction known using converge.induct automaton keys with
  | case1 known next stable =>
      dsimp only [next] at stable
      refine ⟨0, ?_⟩
      rw [converge.eq_def]
      simp only [dite_eq_left stable, sweeps]
  | case2 known next unstable ih =>
      dsimp only [next] at unstable
      obtain ⟨fuel, reached⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [converge.eq_def]
      simp only [dite_eq_right unstable, sweeps]
      exact reached

/-- Every finite value still has a structural accepted witness after convergence. -/
theorem converge_sound [DecidableEq State] (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (keys : List State) (known : State → Option Nat) (sound : Sound automaton known) :
    Sound automaton (converge automaton keys known) := by
  induction known using converge.induct automaton keys with
  | case1 known next stable =>
      dsimp only [next] at stable
      rw [converge.eq_def]
      simpa only [dite_eq_left stable] using sound
  | case2 known next unstable ih =>
      dsimp only [next] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih (sweep_sound automaton plain keys known sound)

/-- Every accepted term bounds a stable table on a finite supported row map. -/
theorem fixed_complete [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State)
    (supported : Supported automaton keys) (known : State → Option Nat)
    (fixed : sweep automaton keys known = known) {state term} (accepted : Accepts automaton state term) :
    ∃ size, known state = some size ∧ size ≤ nodeSize term := by
  have improves : ∀ state edge, edge ∈ automaton state → Improves (edgeMinimum known edge) (known state) := by
    intro state edge member
    have stable := congrFun (sweep_fixed_rows automaton keys known fixed state (supported state edge member)) state
    have result := improves_trans (rowMinimum_improves_member known _ edge member)
      (best_improves_right (known state) _)
    simp only [relax, ite_true] at stable
    rw [← stable]
    exact result
  induction accepted using Accepts.rec
    (motive_2 := fun children terms _ => ∃ size, childSum known children = some size ∧ size ≤ forestSize terms) with
  | @node state edge terms member runs guard ih =>
      obtain ⟨size, present, bound⟩ := ih
      have edgePresent : edgeMinimum known edge = some (size + 1) := by simp [edgeMinimum, present]
      obtain ⟨small, value, less⟩ := improves state edge member (size + 1) edgePresent
      refine ⟨small, value, ?_⟩
      rw [nodeSize]
      exact Nat.le_trans less (Nat.add_le_add_right bound 1)
  | nil => exact ⟨0, rfl, Nat.le_refl _⟩
  | cons child children ih ihs =>
      obtain ⟨size, present, bound⟩ := ih
      obtain ⟨rest, presentRest, boundRest⟩ := ihs
      exact ⟨size + rest, by simp [childSum, present, presentRest], Nat.add_le_add bound boundRest⟩

/-- A computed finite entry is exactly the smallest structural accepted node count. -/
theorem correct [DecidableEq State] (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (keys : List State) (supported : Supported automaton keys) (state : State) (size : Nat) :
    minimumSizes automaton keys state = some size ↔
      (∃ term, Accepts automaton state term ∧ nodeSize term = size) ∧
      (∀ term, Accepts automaton state term → size ≤ nodeSize term) := by
  have sound : Sound automaton (minimumSizes automaton keys) :=
    converge_sound automaton plain keys _ (fun state size impossible => by cases impossible)
  have complete {state term} (accepted : Accepts automaton state term) :=
    fixed_complete automaton keys supported (minimumSizes automaton keys) (converge_fixed automaton keys (fun _ => none)) accepted
  constructor
  · intro present
    refine ⟨sound state size present, ?_⟩
    intro term accepted
    obtain ⟨small, found, bound⟩ := complete accepted
    have same : small = size := Option.some.inj (found.symm.trans present)
    simpa only [same] using bound
  · rintro ⟨⟨term, accepted, exactSize⟩, minimal⟩
    obtain ⟨small, found, bound⟩ := complete accepted
    obtain ⟨witness, witnessAccepted, witnessSize⟩ := sound state small found
    have reverse := minimal witness witnessAccepted
    have same : small = size := by omega
    simpa only [same] using found

/-- A missing minimum is equivalent to absence of every finite structural run. -/
theorem none_iff [DecidableEq State] (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (keys : List State) (supported : Supported automaton keys) (state : State) :
    minimumSizes automaton keys state = none ↔ ∀ term, ¬Accepts automaton state term := by
  constructor
  · intro absent term accepted
    obtain ⟨size, present, _⟩ := fixed_complete automaton keys supported (minimumSizes automaton keys) (converge_fixed automaton keys (fun _ => none)) accepted
    rw [absent] at present
    cases present
  · intro empty
    cases present : minimumSizes automaton keys state with
    | none => rfl
    | some size => exact False.elim (let ⟨term, accepted, _⟩ := ((correct automaton plain keys supported state size).mp present).1; empty term accepted)

/-- Every finite source map converges, even when the state type is not finite. -/
theorem terminates [DecidableEq State] (automaton : Automaton State Symbol) (keys : List State) :
    ∃ fuel, sweeps automaton keys fuel (fun _ => none) = minimumSizes automaton keys ∧
      sweep automaton keys (minimumSizes automaton keys) = minimumSizes automaton keys :=
  ⟨(converge_reached automaton keys (fun _ => none)).choose,
    (converge_reached automaton keys (fun _ => none)).choose_spec, converge_fixed automaton keys _⟩

end MicroCFTA.SourceRowsMinimum
