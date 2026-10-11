import MicroCFTA.MinimumWitness

/-!
# Grouped recursive key and minimum discovery

The source retains each reached key and its smallest discovered size. A key
can be present without a finite member. Two optional entries per key record
these independent facts. Every changed pass decreases the number of missing
entries, then the sum of finite sizes. A finite key domain therefore suffices
for termination; no bound on the initial discovered sizes is required.
-/

namespace MicroCFTA.GroupedProbe
open MinimumSize

/-- Outer absence is an undiscovered key; inner absence is a key without a finite member. -/
abbrev Table (Key : Type) := Key → Option (Option Nat)

/-- `Map.unionWith minimumOf` preserves both discovered keys and finite minima. -/
def join : Option (Option Nat) → Option (Option Nat) → Option (Option Nat)
  | none, right => right
  | left, none => left
  | some left, some right => some (best left right)

/-- One source discovery pass rebuilds the family, then joins its entries with the previous map. -/
def step (build : Table Key → Table Key) (known : Table Key) : Table Key :=
  fun key => join (known key) (build known key)

/-- Encode key presence and finite minimum as separate optional-size entries. -/
def entries (known : Table Key) : Sum Key Key → Option Nat
  | .inl key => (known key).map (fun _ => 0)
  | .inr key => (known key).join

/-- Both components of a joined key refine their previous entries. -/
theorem join_refines (left right : Option (Option Nat)) :
    Improves (left.map (fun _ => 0)) ((join left right).map (fun _ => 0)) ∧
      Improves left.join (join left right).join := by
  cases left with
  | none =>
      constructor
      · intro size found
        cases found
      · intro size found
        cases found
  | some left =>
      cases right with
      | none => exact ⟨improves_refl _, improves_refl _⟩
      | some right => exact ⟨improves_refl _, best_improves_left left right⟩

/-- Rebuilding arbitrary finite-key bodies cannot remove keys or increase an established minimum. -/
theorem step_refines (build : Table Key → Table Key) (known : Table Key) :
    Refines (entries known) (entries (step build known)) := by
  intro entry
  cases entry with
  | inl key => exact (join_refines (known key) (build known key)).1
  | inr key => exact (join_refines (known key) (build known key)).2

/-- The two encoded entries distinguish every map entry, including present empty keys. -/
theorem entries_injective (left right : Table Key) (same : entries left = entries right) : left = right := by
  funext key
  have presence := congrFun same (.inl key)
  have minimum := congrFun same (.inr key)
  cases leftFound : left key <;> cases rightFound : right key <;> simp_all [entries]

/-- Store both measurable entries for every key in the finite domain. -/
def domain (keys : List Key) : List (Sum Key Key) := keys.map Sum.inl ++ keys.map Sum.inr

/-- A complete key list gives a complete entry list. -/
theorem domain_complete (keys : List Key) (complete : ∀ key, key ∈ keys) : ∀ entry, entry ∈ domain keys := by
  intro entry
  cases entry <;> simp [domain, complete]

/-- Compare the actual key map, including entries that have no finite minimum. -/
def sameTable (keys : List Key) (left right : Table Key) : Bool :=
  keys.all (fun key => decide (left key = right key))

/-- The finite comparison stops exactly at map equality. -/
theorem sameTable_correct (keys : List Key) (complete : ∀ key, key ∈ keys) (left right : Table Key) :
    sameTable keys left right = true ↔ left = right := by
  constructor
  · intro same
    funext key
    exact of_decide_eq_true (List.all_eq_true.mp same key (complete key))
  · intro same
    subst right
    simp [sameTable]

/-- Every changed discovery pass strictly decreases the finite lexicographic measure. -/
theorem step_decreases (keys : List Key) (complete : ∀ key, key ∈ keys)
    (build : Table Key → Table Key) (known : Table Key) (different : step build known ≠ known) :
    missing (domain keys) (entries (step build known)) < missing (domain keys) (entries known) ∨
      (missing (domain keys) (entries (step build known)) = missing (domain keys) (entries known) ∧
        total (domain keys) (entries (step build known)) < total (domain keys) (entries known)) := by
  have measure := measure_refines (domain keys) (entries known) (entries (step build known)) (step_refines build known)
  by_cases sameMissing : missing (domain keys) (entries (step build known)) = missing (domain keys) (entries known)
  · right
    refine ⟨sameMissing, ?_⟩
    obtain ⟨weak, equal⟩ := measure.2 sameMissing
    have unequal : total (domain keys) (entries (step build known)) ≠ total (domain keys) (entries known) := by
      intro sameTotal
      apply different
      apply entries_injective
      funext entry
      exact (equal sameTotal entry (domain_complete keys complete entry)).symm
    omega
  · exact Or.inl (by omega)

/-- The source key-discovery loop terminates for every total builder over finitely many keys. -/
def converge (keys : List Key) (complete : ∀ key, key ∈ keys)
    (build : Table Key → Table Key) (known : Table Key) : Table Key :=
  let grown := step build known
  if _stable : sameTable keys grown known = true then known
  else converge keys complete build grown
termination_by (missing (domain keys) (entries known), total (domain keys) (entries known))
decreasing_by
  have different : step build known ≠ known := by
    intro equal
    exact _stable ((sameTable_correct keys complete _ _).mpr equal)
  rcases step_decreases keys complete build known different with fewer | ⟨same, smaller⟩
  · exact Prod.Lex.left _ _ fewer
  · rw [same]
    exact Prod.Lex.right _ smaller

/-- Convergence returns a stable union of all keys and minima reached by the final body. -/
theorem converge_fixed (keys : List Key) (complete : ∀ key, key ∈ keys)
    (build : Table Key → Table Key) (known : Table Key) :
    step build (converge keys complete build known) = converge keys complete build known := by
  induction known using converge.induct keys complete build with
  | case1 known grown stable =>
      dsimp only [grown] at stable
      rw [converge.eq_def]
      simp only [dite_eq_left stable]
      exact (sameTable_correct keys complete _ _).mp stable
  | case2 known grown unstable ih =>
      dsimp only [grown] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih

/-- The complete discovery loop preserves every previously known key and minimum bound. -/
theorem converge_refines (keys : List Key) (complete : ∀ key, key ∈ keys)
    (build : Table Key → Table Key) (known : Table Key) :
    Refines (entries known) (entries (converge keys complete build known)) := by
  induction known using converge.induct keys complete build with
  | case1 known grown stable =>
      dsimp only [grown] at stable
      rw [converge.eq_def]
      simp only [dite_eq_left stable]
      exact fun entry => improves_refl _
  | case2 known grown unstable ih =>
      dsimp only [grown] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact MinimumSize.refines_trans (step_refines build known) ih

/-- A family that adds the successor of every reached natural key can reach infinitely many keys. -/
def successorBuilder (known : Table Nat) (key : Nat) : Option (Option Nat) :=
  if key = 0 then some (some 1) else known (key - 1)

/-- The first `count` natural keys, all with a finite member of size one. -/
def keyPrefix (count : Nat) : Table Nat := fun key => if key < count then some (some 1) else none

/-- One source discovery pass adds exactly the next key of the unbounded family. -/
theorem successor_step (count : Nat) : step successorBuilder (keyPrefix count) = keyPrefix (count + 1) := by
  funext key
  by_cases zero : key = 0
  · subst key
    cases count <;> simp [step, successorBuilder, keyPrefix, join, best]
  · by_cases before : key < count
    · have predecessor : key - 1 < count := by omega
      have after : key < count + 1 := by omega
      simp [step, successorBuilder, keyPrefix, join, best, zero, before, predecessor, after]
    · by_cases predecessor : key - 1 < count
      · have after : key < count + 1 := by omega
        simp [step, successorBuilder, keyPrefix, join, zero, before, predecessor, after]
      · have after : ¬ key < count + 1 := by omega
        simp [step, successorBuilder, keyPrefix, join, zero, before, predecessor, after]

/-- The finite-key premise cannot be removed: this total builder never stabilizes at any finite pass. -/
theorem successor_never_stable (count : Nat) : step successorBuilder (keyPrefix count) ≠ keyPrefix count := by
  intro same
  rw [successor_step] at same
  have key := congrFun same count
  simp [keyPrefix] at key

end MicroCFTA.GroupedProbe
