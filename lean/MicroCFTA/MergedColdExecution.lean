import MicroCFTA.MergedColdInventory

/-!
# Total chronological execution of available cold queries

An arbitrary selector can choose an available value from the current
prepared cache. The actual source unfolding completes at every step.
The resulting schedule supplies the trace premises used by the finite
inventory proof. No eager preparation pass is required.
-/
namespace MicroCFTA.MergedColdExecution
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts
open MergedPhysicalWarmup MergedColdUnfolding

/-- A current physical cache carries its source invariants and preparation property. -/
abbrev Configuration (Symbol Guard : Type) :=
  {state : State Symbol Guard // Facts state ∧ Prepared state}

/-- A selector can inspect the current cache and choose any available value. -/
abbrev Selector (Symbol Guard : Type) :=
  (current : Configuration Symbol Guard) → {value : Value Symbol Guard // Available current.val value}

/-- Each selected cold query has an actual completed next configuration. -/
theorem next_exists [DecidableEq (EdgeKey Symbol Guard)] (select : Selector Symbol Guard)
    (current : Configuration Symbol Guard) :
    ∃ next : Configuration Symbol Guard × Value Symbol Guard,
      InternedStoredSubstitution.unfold (select current).val current.val = .done next.2 next.1.val := by
  obtain ⟨result, after, done⟩ := unfold_complete (select current).val current.val current.property.2 (select current).property
  have verified := InternedStoredSubstitution.unfold_verified (select current).val current.val
    current.property.1 (select current).property
  have facts : Facts after := by simpa only [done, Outcome.state] using verified.facts
  have prepared : Prepared after := by
    have unchanged := unfold_noNewMu (select current).val current.val current.property.2 (select current).property
    simpa only [done, Outcome.state] using current.property.2.preserve unchanged
  exact ⟨(⟨after, facts, prepared⟩, result), done⟩

/-- Retain one actual next result and its returned physical cache. -/
noncomputable def next [DecidableEq (EdgeKey Symbol Guard)] (select : Selector Symbol Guard)
    (current : Configuration Symbol Guard) : Configuration Symbol Guard × Value Symbol Guard :=
  Classical.choose (next_exists select current)

/-- The selected next result agrees exactly with the source unfolding. -/
theorem next_done [DecidableEq (EdgeKey Symbol Guard)] (select : Selector Symbol Guard)
    (current : Configuration Symbol Guard) :
    InternedStoredSubstitution.unfold (select current).val current.val =
      .done (next select current).2 (next select current).1.val :=
  Classical.choose_spec (next_exists select current)

/-- Execute queries in their actual chronological allocation order. -/
noncomputable def configurationAt [DecidableEq (EdgeKey Symbol Guard)] (select : Selector Symbol Guard)
    (initial : Configuration Symbol Guard) : Nat → Configuration Symbol Guard
  | 0 => initial
  | index + 1 => (next select (configurationAt select initial index)).1

/-- Every available selector generates a complete infinite source schedule. -/
noncomputable def schedule [DecidableEq (EdgeKey Symbol Guard)] (select : Selector Symbol Guard)
    (initial : Configuration Symbol Guard) : Schedule Symbol Guard where
  state index := (configurationAt select initial index).val
  input index := (select (configurationAt select initial index)).val
  result index := (next select (configurationAt select initial index)).2
  available index := (select (configurationAt select initial index)).property
  done index := next_done select (configurationAt select initial index)

/-- The schedule starts in the supplied cold cache. -/
theorem initial_state [DecidableEq (EdgeKey Symbol Guard)] (select : Selector Symbol Guard)
    (initial : Configuration Symbol Guard) : (schedule select initial).state 0 = initial.val := rfl

/-- Total execution of any available selection policy eventually has a constant physical cache. -/
theorem execution_stabilizes [DecidableEq (EdgeKey Symbol Guard)] (select : Selector Symbol Guard)
    (initial : Configuration Symbol Guard) :
    ∃ bound, ∀ index, bound ≤ index →
      (schedule select initial).state index = (schedule select initial).state bound := by
  obtain ⟨bound, stable, _⟩ := stabilizes (schedule select initial) initial.property.1 initial.property.2
  exact ⟨bound, stable⟩

end MicroCFTA.MergedColdExecution
