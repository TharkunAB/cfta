import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.SourcePruningEnumerationNonterminalCacheBounds
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# Exact own-prefix and residual scalars

Own classes append empty pending buckets. Residual recording changes only
obligations. Finalization replaces one stored value by an enumerated fragment
and removes its pending mass. These observers use actual cache equations.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState EnumerationCorrectness
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- Every actual own-class traversal has the exact existing suspended-state endpoint. -/
theorem suspendMany_core
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (tries : List EqualityTrie.Trie) (before : Cached) (own : List Suspended) (after : Cached)
    (observed : suspendMany heap tries before = some (own, after)) :
    after.core = suspendedState tries.length before.core := by
  induction tries generalizing before own after with
  | nil =>
      simp only [suspendMany, Option.some.injEq, Prod.mk.injEq] at observed
      obtain ⟨_ownSame, afterSame⟩ := observed
      subst after
      rfl
  | cons trie rest ih =>
      let middle : Cached := ⟨allocated none before.core, before.expandable, before.waiting⟩
      have allocatedNone : SourcePruningEnumerationCachedChild.allocate heap none before =
          some (before.core.counter, middle) := rfl
      simp only [suspendMany, allocatedNone, Option.bind_some, Option.map_eq_some_iff] at observed
      obtain ⟨tail, tailRun, resultSame⟩ := observed
      have afterSame : tail.2 = after := (Prod.mk.inj resultSame).2
      rw [← afterSame]
      simpa only [List.length_cons, suspendedState] using ih middle tail.1 tail.2 tailRun

/-- Empty own-class allocations increase the counter and retain the full suspended mass. -/
theorem suspendedState_scalars (count : Nat) (before : Core) :
    (suspendedState count before).counter = before.counter + count ∧
      suspendedBound (suspendedState count before) = suspendedBound before := by
  induction count generalizing before with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
      obtain ⟨counter, mass⟩ := ih (allocated none before)
      refine ⟨?_, ?_⟩
      · change (suspendedState count (allocated none before)).counter = before.counter + (count + 1)
        rw [counter]
        change before.counter + 1 + count = before.counter + (count + 1)
        omega
      · simpa only [suspendedState, SourcePruningEnumerationCachedPrepare.allocated_mass] using mass

/-- The actual own-class cache equation supplies both exact scalar receipts. -/
theorem suspendMany_scalars
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (tries : List EqualityTrie.Trie) (before : Cached) (own : List Suspended) (after : Cached)
    (observed : suspendMany heap tries before = some (own, after)) :
    after.core.counter = before.core.counter + tries.length ∧
      suspendedBound after.core = suspendedBound before.core := by
  rw [suspendMany_core heap tries before own after observed]
  exact suspendedState_scalars tries.length before.core

/-- A successful prepared singleton retains its actual projection and exact own-prefix scalars. -/
theorem prepare_scalars
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (before after : Cached) (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (result : Symbol × List (Node × List Suspended ×
      Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (observed : prepare heap scs edge before = some [(result, after)]) :
    arityAllows edge.children.length scs = true ∧
      after.core = suspendedState tries.length before.core ∧
      after.core.counter = before.core.counter + tries.length ∧
      suspendedBound after.core = suspendedBound before.core := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [prepare, allowed, ↓reduceIte, projected, Option.map_eq_some_iff] at observed
    obtain ⟨ownResult, ownRun, resultSame⟩ := observed
    have afterSame : ownResult.2 = after := (Prod.mk.inj (List.cons.inj resultSame).1).2
    have core := suspendMany_core heap tries before ownResult.1 ownResult.2 ownRun
    have scalars := suspendMany_scalars heap tries before ownResult.1 ownResult.2 ownRun
    exact ⟨allowed, afterSame ▸ core, afterSame ▸ scalars⟩
  · simp [prepare, allowed] at observed

end MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The actual residual finish preserves the counter and all suspended occurrences. -/
theorem finish_scalars (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    (finish residual fragment before).core.counter = before.core.counter ∧
      suspendedBound (finish residual fragment before).core = suspendedBound before.core :=
  ⟨rfl, rfl⟩

end MicroCFTA.SourcePruningEnumerationSelectedEdge

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

private theorem sum_map_set_zero_le {α : Type} (weight : α → Nat) (replacement : α)
    (replacementZero : weight replacement = 0) (values : List α) (index : Nat) :
    ((values.set index replacement).map weight).sum ≤ (values.map weight).sum := by
  induction values generalizing index with
  | nil => simp
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.set_cons_zero, List.map_cons, List.sum_cons, replacementZero]
          omega
      | succ index =>
          simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
          exact Nat.add_le_add_left (ih index) _

/-- Writing an enumerated fragment cannot add pending mass, including at an absent target. -/
theorem enumerated_mass_le (before : Core) (target : Nat) (fragment : Fragments.Fragment Symbol) :
    suspendedBound {before with values := before.values.set target (.enumerated fragment)} ≤
      suspendedBound before := by
  exact sum_map_set_zero_le (fun value : UVarValue Symbol => match value with
    | .unenumerated _ scs => scs.length
    | _ => 0) (.enumerated fragment) rfl before.values target

/-- Every actual finalization keeps the counter and does not increase suspended mass. -/
theorem run_scalars
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : Cached)
    (observed : run heap fuel target fragment before = some after) :
    after.core.counter = before.core.counter ∧ suspendedBound after.core ≤ suspendedBound before.core := by
  unfold run at observed
  obtain ⟨old, _stored, written⟩ := Option.bind_eq_some_iff.mp observed
  unfold SourcePruningEnumerationNativeIndex.write at written
  obtain ⟨flag, _classified, written⟩ := Option.bind_eq_some_iff.mp written
  obtain ⟨removed, _removedCounts, written⟩ := Option.bind_eq_some_iff.mp written
  obtain ⟨saved, _savedCounts, afterSame⟩ := Option.bind_eq_some_iff.mp written
  have cacheSame := Option.some.inj afterSame
  subst after
  exact ⟨rfl, enumerated_mass_le before.core target fragment⟩

end MicroCFTA.SourcePruningEnumerationFinalize
