import MicroCFTA.EqualityFixedProjectionInvariant
import MicroCFTA.FiniteRowIntersection

/-!
# A finite bound for one projected binary equality class

The first pass can remove rows. Every later pass retains all rows at each
original occurrence. Count the missing occurrence-row pairs after that
first pass. A changing pass strictly decreases this finite count.

The row relation can describe endpoints with children. The proof requires
commutativity, admitted diagonal rows, and a finite complete row inventory.
It does not require associativity or an arbitrary-target narrowing rank.
It covers one fixed binary class. Other classes can change its endpoints.
-/
namespace MicroCFTA.EqualityFixedProjectionTermination
open EqualityFixedProjectionInvariant

/-- Keep each endpoint occurrence at its original position. -/
abbrev State (Left Right Row : Type) := (Left → Rows Row) × (Right → Rows Row)

/-- Read both projections before the two reciprocal occurrence edits. -/
noncomputable def step (join : Row → Row → Row → Prop)
    (state : State Left Right Row) : State Left Right Row :=
  (edit join state.1 (project state.2), edit join state.2 (project state.1))

/-- A finite inventory counts both sides without identifying their occurrences. -/
def member (state : State Left Right Row) : (Sum Left Right × Row) → Prop
  | (.inl index, row) => state.1 index row
  | (.inr index, row) => state.2 index row

/-- The indexed row predicate determines the complete occurrence state. -/
theorem member_injective (left right : State Left Right Row)
    (same : member left = member right) : left = right := by
  apply Prod.ext
  · funext index row
    exact congrFun same (.inl index, row)
  · funext index row
    exact congrFun same (.inr index, row)

/-- All occurrence rows survive from the first pass onward. -/
theorem after_first_included (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (state : State Left Right Row) (entry : Sum Left Right × Row)
    (present : member (step join state) entry) : member (step join (step join state)) entry := by
  rcases entry with ⟨index, row⟩
  cases index with
  | inl index => exact post_first_expands join diagonal symmetric state.1 state.2 index row present
  | inr index => exact post_first_expands join diagonal symmetric state.2 state.1 index row present

/-- Missing occurrence-row pairs form a natural progress measure after the first pass. -/
noncomputable def potential (inventory : List (Sum Left Right × Row))
    (state : State Left Right Row) : Nat :=
  inventory.length - FiniteRowIntersection.count inventory (member state)

/-- A changing later pass strictly decreases the remaining finite inventory. -/
theorem after_first_strict (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (inventory : List (Sum Left Right × Row)) (complete : ∀ entry, entry ∈ inventory)
    (state : State Left Right Row) (changed : step join (step join state) ≠ step join state) :
    potential inventory (step join (step join state)) < potential inventory (step join state) := by
  have different : member (step join state) ≠ member (step join (step join state)) :=
    fun same => changed (member_injective _ _ same).symm
  have grows := FiniteRowIntersection.count_strict inventory complete _ _
    (after_first_included join diagonal symmetric state) different
  have bound := FiniteRowIntersection.count_bound inventory (member (step join (step join state)))
  unfold potential
  omega

/-- Follow the source equality check with an explicit finite fuel bound. -/
noncomputable def run (join : Row → Row → Row → Prop) :
    Nat → State Left Right Row → Option (State Left Right Row)
  | 0, _ => none
  | fuel + 1, state => by
      classical
      exact let next := step join state
        if next = state then some state else run join fuel next

/-- The remaining occurrence-row inventory bounds every run after the first pass. -/
theorem run_after_first (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (inventory : List (Sum Left Right × Row)) (complete : ∀ entry, entry ∈ inventory)
    (fuel : Nat) (state : State Left Right Row)
    (enough : potential inventory (step join state) < fuel) :
    ∃ result, run join fuel (step join state) = some result ∧ step join result = result := by
  classical
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      by_cases same : step join (step join state) = step join state
      · exact ⟨step join state, by simp only [run, same, ↓reduceIte], same⟩
      · have lower := after_first_strict join diagonal symmetric inventory complete state same
        have remaining : potential inventory (step join (step join state)) < fuel := by omega
        obtain ⟨result, finished, fixed⟩ := ih (step join state) remaining
        exact ⟨result, by simpa only [run, same, ↓reduceIte] using finished, fixed⟩

/-- One initial pass and the remaining inventory suffice, including the final equality check. -/
theorem run_bounded (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (inventory : List (Sum Left Right × Row)) (complete : ∀ entry, entry ∈ inventory)
    (state : State Left Right Row) :
    ∃ result, run join (potential inventory (step join state) + 2) state = some result ∧
      step join result = result := by
  classical
  by_cases same : step join state = state
  · exact ⟨state, by simp only [run, same, ↓reduceIte], same⟩
  · obtain ⟨result, finished, fixed⟩ := run_after_first join diagonal symmetric inventory complete
      (potential inventory (step join state) + 1) state (Nat.lt_succ_self _)
    exact ⟨result, by simpa only [run, same, ↓reduceIte] using finished, fixed⟩

end MicroCFTA.EqualityFixedProjectionTermination
