import MicroCFTA.GroupedProbe

/-!
# Least attained minima for recursive key families

The family body uses finite size sources, keyed occurrences, pay, choices,
and products. The key-discovery driver executes these operations. Independent
finite derivations specify each key's language. Every stored finite minimum
has a derivation, and every finite derivation reaches a retained key.
-/

namespace MicroCFTA.GroupedMinimum
open GroupedProbe MinimumSize

/-- Keyed source operations that determine existence and minimum size. -/
inductive Expression (Key : Type) where
  | source (sizes : List Nat)
  | occurrence (key : Key)
  | pay (inner : Expression Key)
  | choice (left right : Expression Key)
  | product (left right : Expression Key)

/-- Products require both keys to exist and both minima to be finite before they have a finite minimum. -/
def productEntry : Option (Option Nat) → Option (Option Nat) → Option (Option Nat)
  | some left, some right => some (RecursionProbe.productMinimum left right)
  | _, _ => none

/-- Evaluate the same key-presence and minimum operations as the source family builder. -/
def evaluate : Expression Key → Table Key → Option (Option Nat)
  | .source sizes, _ => some sizes.min?
  | .occurrence key, known => known key
  | .pay inner, known => (evaluate inner known).map (fun minimum => minimum.map (· + 1))
  | .choice left right, known => join (evaluate left known) (evaluate right known)
  | .product left right, known => productEntry (evaluate left known) (evaluate right known)

/-- Rebuild each declared key from its expression and the current family probes. -/
def build (program : Key → Expression Key) (known : Table Key) : Table Key :=
  fun key => evaluate (program key) known

/-- Finite derivations unfold keyed occurrences without using a computed minimum table. -/
inductive Derives (program : Key → Expression Key) : Expression Key → Nat → Prop where
  | source (sizes : List Nat) (size : Nat) (member : size ∈ sizes) : Derives program (.source sizes) size
  | occurrence (key : Key) (size : Nat) (inner : Derives program (program key) size) :
      Derives program (.occurrence key) size
  | pay (inner : Expression Key) (size : Nat) (child : Derives program inner size) :
      Derives program (.pay inner) (size + 1)
  | left (left right : Expression Key) (size : Nat) (child : Derives program left size) :
      Derives program (.choice left right) size
  | right (left right : Expression Key) (size : Nat) (child : Derives program right size) :
      Derives program (.choice left right) size
  | product (left right : Expression Key) (leftSize rightSize : Nat)
      (first : Derives program left leftSize) (second : Derives program right rightSize) :
      Derives program (.product left right) (leftSize + rightSize)

/-- Every retained finite entry comes from one of the two maps. -/
theorem join_finite (left right : Option (Option Nat)) (size : Nat)
    (found : join left right = some (some size)) : left = some (some size) ∨ right = some (some size) := by
  cases left with
  | none => exact Or.inr found
  | some left =>
      cases right with
      | none => exact Or.inl found
      | some right =>
          have finite := Option.some.inj found
          rcases best_source left right size finite with fromLeft | fromRight
          · exact Or.inl (congrArg some fromLeft)
          · exact Or.inr (congrArg some fromRight)

/-- A table is sound when every stored finite minimum has an independent derivation. -/
def Sound (program : Key → Expression Key) (known : Table Key) : Prop :=
  ∀ key size, known key = some (some size) → Derives program (program key) size

/-- Each expression operation constructs a derivation for its reported finite minimum. -/
theorem evaluate_sound (program : Key → Expression Key) (known : Table Key) (sound : Sound program known)
    (expression : Expression Key) (size : Nat) (found : evaluate expression known = some (some size)) :
    Derives program expression size := by
  induction expression generalizing size with
  | source sizes => exact .source sizes size (List.min?_eq_some_iff.mp (Option.some.inj found)).1
  | occurrence key => exact .occurrence key size (sound key size found)
  | pay inner ih =>
      cases outer : evaluate inner known with
      | none => simp [evaluate, outer] at found
      | some minimum =>
          cases minimum with
          | none => simp [evaluate, outer] at found
          | some smaller =>
              have same : size = smaller + 1 := by simpa [evaluate, outer] using found.symm
              exact same ▸ Derives.pay inner smaller (ih smaller outer)
  | choice left right ihl ihr =>
      rcases join_finite _ _ size found with fromLeft | fromRight
      · exact .left left right size (ihl size fromLeft)
      · exact .right left right size (ihr size fromRight)
  | product left right ihl ihr =>
      cases leftEntry : evaluate left known with
      | none => simp [evaluate, productEntry, leftEntry] at found
      | some leftMinimum =>
          cases rightEntry : evaluate right known with
          | none => simp [evaluate, productEntry, leftEntry, rightEntry] at found
          | some rightMinimum =>
              cases leftMinimum with
              | none => simp [evaluate, productEntry, RecursionProbe.productMinimum, leftEntry, rightEntry] at found
              | some leftSize =>
                  cases rightMinimum with
                  | none => simp [evaluate, productEntry, RecursionProbe.productMinimum, leftEntry, rightEntry] at found
                  | some rightSize =>
                      have same : size = leftSize + rightSize := by
                        simpa [evaluate, productEntry, RecursionProbe.productMinimum, leftEntry, rightEntry] using found.symm
                      exact same ▸ Derives.product left right leftSize rightSize (ihl leftSize leftEntry) (ihr rightSize rightEntry)

/-- Rebuilding and joining the family preserves witnessed finite minima. -/
theorem step_sound (program : Key → Expression Key) (known : Table Key) (sound : Sound program known) :
    Sound program (step (build program) known) := by
  intro key size found
  rcases join_finite _ _ size found with previous | rebuilt
  · exact sound key size previous
  · exact evaluate_sound program known sound (program key) size rebuilt

/-- The complete source discovery loop cannot invent a productive key or finite minimum. -/
theorem converge_sound (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Expression Key)
    (known : Table Key) (sound : Sound program known) : Sound program (converge keys complete (build program) known) := by
  induction known using converge.induct keys complete (build program) with
  | case1 known grown stable =>
      dsimp only [grown] at stable
      rw [converge.eq_def]
      simpa only [dite_eq_left stable] using sound
  | case2 known grown unstable ih =>
      dsimp only [grown] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih (step_sound program known sound)

/-- Joining keeps or lowers each finite minimum from the first map. -/
theorem join_left_bound (left right : Option (Option Nat)) (size : Nat) (found : left = some (some size)) :
    ∃ lower, join left right = some (some lower) ∧ lower ≤ size := by
  subst left
  cases right with
  | none => exact ⟨size, rfl, Nat.le_refl _⟩
  | some right =>
      obtain ⟨lower, kept, bound⟩ := best_improves_left (some size) right size rfl
      exact ⟨lower, congrArg some kept, bound⟩

/-- Joining keeps or lowers each finite minimum reached by the rebuilt body. -/
theorem join_right_bound (left right : Option (Option Nat)) (size : Nat) (found : right = some (some size)) :
    ∃ lower, join left right = some (some lower) ∧ lower ≤ size := by
  subst right
  cases left with
  | none => exact ⟨size, rfl, Nat.le_refl _⟩
  | some left =>
      obtain ⟨lower, kept, bound⟩ := best_improves_right left (some size) size rfl
      exact ⟨lower, congrArg some kept, bound⟩

/-- A stable discovered table includes each finite minimum reached by its final body. -/
theorem stable_bound (program : Key → Expression Key) (known : Table Key)
    (fixed : step (build program) known = known) (key : Key) (size : Nat)
    (found : evaluate (program key) known = some (some size)) :
    ∃ lower, known key = some (some lower) ∧ lower ≤ size := by
  obtain ⟨lower, kept, bound⟩ := join_right_bound (known key) (evaluate (program key) known) size found
  have same := congrFun fixed key
  change join (known key) (evaluate (program key) known) = known key at same
  exact ⟨lower, same ▸ kept, bound⟩

/-- Every independent finite derivation has a discovered expression minimum at or below its size. -/
theorem evaluate_complete (program : Key → Expression Key) (known : Table Key)
    (fixed : step (build program) known = known) (expression : Expression Key) (size : Nat)
    (derived : Derives program expression size) :
    ∃ lower, evaluate expression known = some (some lower) ∧ lower ≤ size := by
  induction derived with
  | source sizes size member =>
      cases found : sizes.min? with
      | none => have empty := List.min?_eq_none_iff.mp found; simp [empty] at member
      | some lower => exact ⟨lower, congrArg some found, (List.min?_eq_some_iff.mp found).2 size member⟩
  | occurrence key size inner ih =>
      obtain ⟨lower, found, bound⟩ := ih
      obtain ⟨smaller, kept, smallerBound⟩ := stable_bound program known fixed key lower found
      exact ⟨smaller, kept, by omega⟩
  | pay inner size child ih =>
      obtain ⟨lower, found, bound⟩ := ih
      exact ⟨lower + 1, by simp [evaluate, found], by omega⟩
  | left left right size child ih =>
      obtain ⟨lower, found, bound⟩ := ih
      obtain ⟨smaller, kept, smallerBound⟩ := join_left_bound (evaluate left known) (evaluate right known) lower found
      exact ⟨smaller, kept, by omega⟩
  | right left right size child ih =>
      obtain ⟨lower, found, bound⟩ := ih
      obtain ⟨smaller, kept, smallerBound⟩ := join_right_bound (evaluate left known) (evaluate right known) lower found
      exact ⟨smaller, kept, by omega⟩
  | product left right leftSize rightSize first second ihl ihr =>
      obtain ⟨leftMinimum, leftFound, leftBound⟩ := ihl
      obtain ⟨rightMinimum, rightFound, rightBound⟩ := ihr
      exact ⟨leftMinimum + rightMinimum,
        by simp [evaluate, productEntry, RecursionProbe.productMinimum, leftFound, rightFound], by omega⟩

/-- The public key discovery starts with no keys, as in `recurGrouped`. -/
def discover (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Expression Key) : Table Key :=
  converge keys complete (build program) (fun _ => none)

/-- Every reported finite key minimum is attained. -/
theorem discover_sound (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Expression Key) :
    Sound program (discover keys complete program) :=
  converge_sound keys complete program _ (by intro key size found; cases found)

/-- Every key with a finite derivation is discovered with a minimum no larger than that derivation. -/
theorem discover_complete (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Expression Key)
    (key : Key) (size : Nat) (derived : Derives program (program key) size) :
    ∃ lower, discover keys complete program key = some (some lower) ∧ lower ≤ size := by
  have fixed := converge_fixed keys complete (build program) (fun _ => none)
  obtain ⟨lower, found, bound⟩ := evaluate_complete program (discover keys complete program) fixed (program key) size derived
  obtain ⟨smaller, kept, smallerBound⟩ := stable_bound program (discover keys complete program) fixed key lower found
  exact ⟨smaller, kept, by omega⟩

/-- The final stored number is exactly the least attained size at the key. -/
theorem discover_minimum (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Expression Key)
    (key : Key) (size : Nat) :
    discover keys complete program key = some (some size) ↔
      Derives program (program key) size ∧ ∀ other, Derives program (program key) other → size ≤ other := by
  constructor
  · intro found
    refine ⟨discover_sound keys complete program key size found, ?_⟩
    intro other derived
    obtain ⟨lower, kept, bound⟩ := discover_complete keys complete program key other derived
    have equal := Option.some.inj (Option.some.inj (found.symm.trans kept))
    exact equal ▸ bound
  · rintro ⟨derived, minimal⟩
    obtain ⟨lower, found, bound⟩ := discover_complete keys complete program key size derived
    have reverse := minimal lower (discover_sound keys complete program key lower found)
    have same : lower = size := by omega
    exact same ▸ found

/-- The source removes discovered keys that have no finite minimum. -/
def liveKeys (keys : List Key) (known : Table Key) : List Key := keys.filter fun key => (known key).join.isSome

/-- The final live-key filter removes exactly the keys with no finite derivation. -/
theorem liveKeys_exact (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Expression Key) (key : Key) :
    key ∈ liveKeys keys (discover keys complete program) ↔ ∃ size, Derives program (program key) size := by
  constructor
  · intro present
    have finite := (List.mem_filter.mp present).2
    cases found : discover keys complete program key with
    | none => simp [found] at finite
    | some minimum =>
        cases minimum with
        | none => simp [found] at finite
        | some size => exact ⟨size, discover_sound keys complete program key size found⟩
  · rintro ⟨size, derived⟩
    obtain ⟨lower, found, _⟩ := discover_complete keys complete program key size derived
    simp [liveKeys, complete, found]

end MicroCFTA.GroupedMinimum
