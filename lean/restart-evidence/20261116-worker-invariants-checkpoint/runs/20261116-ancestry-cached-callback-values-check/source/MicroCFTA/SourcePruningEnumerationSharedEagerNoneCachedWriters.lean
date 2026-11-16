import MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters
open EnumerationState EnumerationCorrectness
open SourcePruningEnumerationSharedEagerNoneBuckets
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Edge" => InternedConstructorTemplates.EdgeValue Symbol Constraint
local notation "Native" => InternedConstructorTemplates.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "OwnRows" => List ((Symbol × List (Node × List Suspended ×
  Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint) × Cached)
set_option autoImplicit false

private theorem indexed_write_core (heap : Native) (fuel target : Nat)
    (value : UVarValue Symbol) (gained lost : List Suspended) (before after : Cached)
    (actual : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost before = some after) :
    after.core = {before.core with values := before.core.values.set target value} := by
  unfold SourcePruningEnumerationNativeIndex.write at actual
  obtain ⟨flag, _classified, actual⟩ := Option.bind_eq_some_iff.mp actual
  obtain ⟨removed, _removed, actual⟩ := Option.bind_eq_some_iff.mp actual
  obtain ⟨saved, _saved, actual⟩ := Option.bind_eq_some_iff.mp actual
  cases actual
  rfl

/-- The initial root slot has a supplied handle and no missing-domain bucket. -/
theorem initial_none_buckets (root : Nat) : NoneBucketsEmpty (EnumerationState.initial root) := by
  intro uv scs stored
  cases uv <;> simp [EnumerationState.initial] at stored

/-- The actual cached allocator uses the same literal empty-bucket allocation. -/
theorem cached_allocate_none_buckets (heap : Native) (node : Option Nat)
    (before after : Cached) (uv : Nat) (initial : NoneBucketsEmpty before.core)
    (actual : SourcePruningEnumerationCachedChild.allocate heap node before = some (uv, after)) :
    NoneBucketsEmpty after.core := by
  simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at actual
  obtain ⟨flag, _classified, same⟩ := actual
  have coreSame := congrArg (fun result : Nat × Cached => result.2.core) same
  rw [← coreSame]
  exact allocated_none_buckets node before.core initial

/-- Every actual own-class suspension allocation retains the property. -/
theorem own_suspensions_none_buckets (heap : Native) (tries : List EqualityTrie.Trie)
    (before after : Cached) (own : List Suspended) (initial : NoneBucketsEmpty before.core)
    (actual : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (own, after)) :
    NoneBucketsEmpty after.core := by
  induction tries generalizing before after own with
  | nil =>
      have same := Option.some.inj actual
      have afterSame : after = before := (congrArg Prod.snd same).symm
      rw [afterSame]
      exact initial
  | cons trie rest ih =>
      let middle : Cached := ⟨allocated none before.core, before.expandable, before.waiting⟩
      have allocatedNone : SourcePruningEnumerationCachedChild.allocate heap none before =
          some (before.core.counter, middle) := rfl
      simp only [SourcePruningEnumerationCachedOwn.suspendMany, allocatedNone,
        Option.bind_some, Option.map_eq_some_iff] at actual
      obtain ⟨tail, tailRun, resultSame⟩ := actual
      have afterSame : after = tail.2 := (congrArg Prod.snd resultSame).symm
      rw [afterSame]
      have middleNone : NoneBucketsEmpty middle.core := allocated_none_buckets none before.core initial
      exact ih middle tail.2 tail.1 middleNone tailRun

/-- Every actual prepared own-class result retains the property. -/
theorem own_prefix_none_buckets (heap : Native) (scs : List Suspended) (edge : Edge)
    (before : Cached) (rows : OwnRows) (initial : NoneBucketsEmpty before.core)
    (actual : SourcePruningEnumerationCachedOwn.prepare heap scs edge before = some rows) :
    ∀ row ∈ rows, NoneBucketsEmpty row.2.core := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected] at actual
        cases actual
    | some fields =>
        obtain ⟨tries, residual⟩ := fields
        simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, Option.map_eq_some_iff] at actual
        obtain ⟨result, suspended, rowsSame⟩ := actual
        intro row member
        rw [← rowsSame] at member
        have rowSame := List.mem_singleton.mp member
        rw [rowSame]
        exact own_suspensions_none_buckets heap tries before result.2 result.1 initial suspended
  · simp only [SourcePruningEnumerationCachedOwn.prepare, ite_eq_right allowed,
      Option.some.injEq] at actual
    rw [← actual]
    intro row impossible
    cases impossible

/-- A successful native indexed Some-handle write retains the property. -/
theorem indexed_some_none_buckets (heap : Native) (fuel target handle : Nat)
    (bucket gained lost : List Suspended) (before after : Cached)
    (initial : NoneBucketsEmpty before.core)
    (actual : SourcePruningEnumerationNativeIndex.write heap fuel target
      (.unenumerated (some handle) bucket) gained lost before = some after) :
    NoneBucketsEmpty after.core := by
  rw [indexed_write_core heap fuel target (.unenumerated (some handle) bucket) gained lost before after actual]
  exact some_write_none_buckets target handle bucket before.core
    {before.core with values := before.core.values.set target (.unenumerated (some handle) bucket)}
    initial ((EnumerationDriver.modify_success _ _ _).mpr rfl)

/-- A successful native indexed fragment write retains the property. -/
theorem indexed_enumerated_none_buckets (heap : Native) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (gained lost : List Suspended) (before after : Cached)
    (initial : NoneBucketsEmpty before.core)
    (actual : SourcePruningEnumerationNativeIndex.write heap fuel target
      (.enumerated fragment) gained lost before = some after) :
    NoneBucketsEmpty after.core := by
  rw [indexed_write_core heap fuel target (.enumerated fragment) gained lost before after actual]
  exact enumerated_write_none_buckets target fragment before.core
    {before.core with values := before.core.values.set target (.enumerated fragment)}
    initial ((EnumerationDriver.modify_success _ _ _).mpr rfl)

/-- Actual captured finalization retains the property at its same full cache. -/
theorem finalize_none_buckets (heap : Native) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : Cached)
    (initial : NoneBucketsEmpty before.core)
    (actual : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    NoneBucketsEmpty after.core := by
  simp only [SourcePruningEnumerationFinalize.run, Option.bind_eq_some_iff] at actual
  obtain ⟨old, _stored, written⟩ := actual
  exact indexed_enumerated_none_buckets heap fuel target fragment [] (EnumerationSchedule.references old)
    (EnumerationExpandableIndex.frame {before.core with expansionAncestry := []} before)
    after (none_buckets_of_values_eq before.core _ initial rfl) written

end MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters

#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters.initial_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters.cached_allocate_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters.own_suspensions_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters.own_prefix_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters.indexed_some_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters.indexed_enumerated_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters.finalize_none_buckets
