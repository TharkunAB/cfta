import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.EnumerationConstruction

/-!
# Program roles through actual own-class allocation

The selected edge prefix calls the existing cached suspendMany action.
The action allocates pure equality slots and retains the old mark set.
The exact core includes the actual recursion-ancestry updates.
No native validity, prepared Packet, or semantic witness is supplied.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesClassAllocation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open InternedConstructorTemplates SourceSynthesisProgramEnumerationRoles
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

local instance classAllocationMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem suspension_indices (heap : NativeHeap) (tries : List EqualityTrie.Trie)
    (before after : Cached) (own : List Suspended)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (own, after)) :
    after.expandable = before.expandable ∧ after.waiting = before.waiting := by
  induction tries generalizing before after own with
  | nil =>
      simp only [SourcePruningEnumerationCachedOwn.suspendMany, Option.some.injEq, Prod.mk.injEq] at observed
      obtain ⟨_ownSame, afterSame⟩ := observed
      subst after
      exact ⟨rfl, rfl⟩
  | cons trie rest ih =>
      let middle : Cached := ⟨allocated none before.core, before.expandable, before.waiting⟩
      have allocatedNone : SourcePruningEnumerationCachedChild.allocate heap none before =
          some (before.core.counter, middle) := rfl
      simp only [SourcePruningEnumerationCachedOwn.suspendMany, allocatedNone,
        Option.bind_some, Option.map_eq_some_iff] at observed
      obtain ⟨tail, tailRun, resultSame⟩ := observed
      have afterSame : tail.2 = after := (Prod.mk.inj resultSame).2
      rw [← afterSame]
      exact ih middle tail.2 tail.1 tailRun

private theorem suspension_values (count : Nat) (before : Core) :
    (suspendedState count before).values =
      before.values ++ List.replicate count (.unenumerated none []) := by
  induction count generalizing before with
  | zero => simp [suspendedState]
  | succ count ih =>
      rw [suspendedState, ih]
      simp [allocated, List.replicate_succ, List.append_assoc]

/-- Actual class suspension preserves old Program marks and identifies every fresh equality slot. -/
theorem suspendMany_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (tries : List EqualityTrie.Trie)
    (before after : Cached) (own : List Suspended) (marked : Nat → Prop)
    (safe : Safe before.core) (slots : ProgramSlots valid literal heap before.core marked)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (own, after)) :
    own = suspendedVars before.core.counter tries ∧
      after = ⟨suspendedState tries.length before.core, before.expandable, before.waiting⟩ ∧
      ExceptT.run ((tries.mapM (EnumerationState.suspend : EqualityTrie.Trie → EnumerateM Symbol Constraint Suspended)) before.core) = [.ok (own, after.core)] ∧
      after.core.counter = before.core.counter + tries.length ∧
      after.core.representatives = before.core.representatives ∧
      Safe after.core ∧ ProgramSlots valid literal heap after.core marked ∧
      (∀ uv, marked uv → Protected uv before.core after.core ∧ Avoids after.core.representatives uv own) ∧
      ∀ offset, offset < tries.length →
        ¬marked (before.core.counter + offset) ∧
        after.core.values[before.core.counter + offset]? = some (.unenumerated none []) ∧
        IsRoot after.core.representatives (before.core.counter + offset) := by
  have ownSame := SourcePruningEnumerationCachedOwn.suspendMany_vars heap tries before own after observed
  have coreSame := SourcePruningEnumerationCachedOwn.suspendMany_core heap tries before own after observed
  have indices := suspension_indices heap tries before after own observed
  have cacheSame : after = ⟨suspendedState tries.length before.core, before.expandable, before.waiting⟩ := by
    cases after with
    | mk afterCore afterExpandable afterWaiting =>
        simp only [EnumerationExpandableIndex.Cached.mk.injEq]
        exact ⟨coreSame, indices.1, indices.2⟩
  have raw : ExceptT.run ((tries.mapM (EnumerationState.suspend : EqualityTrie.Trie → EnumerateM Symbol Constraint Suspended)) before.core) = [.ok (own, after.core)] := by
    rw [ownSame, coreSame]
    exact suspendMany_exact tries before.core
  have counterSame : after.core.counter = before.core.counter + tries.length := by
    rw [coreSame]
    exact suspended_counter tries.length before.core
  have forestSame : after.core.representatives = before.core.representatives := by
    rw [coreSame]
    exact EnumerationConstruction.suspended_forest tries.length before.core
  have afterSafe : Safe after.core := by
    rw [coreSame]
    exact suspension_safe tries.length before.core safe
  have protects : ∀ uv, marked uv → Protected uv before.core after.core := by
    intro uv known
    rw [coreSame]
    exact suspension_protected uv tries.length before.core safe (slots.bounded uv known) (slots.roots uv known)
  have afterSlots : ProgramSlots valid literal heap after.core marked := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro uv known
      have bound := slots.bounded uv known
      rw [counterSame]
      omega
    · intro uv known
      exact (protects uv known).root
    · intro uv known
      change EnumerationReferences.ReferencesAllowed
        (fun target => ¬UnionFind.SameClass after.core.representatives uv target) after.core
      rw [coreSame, EnumerationConstruction.suspended_forest]
      exact EnumerationReferences.suspension_allowed _ tries.length before.core (slots.incoming uv known)
    · intro uv known
      obtain ⟨payload, stored, role⟩ := slots.stored uv known
      exact ⟨payload, (protects uv known).value.trans stored, role⟩
  refine ⟨ownSame, cacheSame, raw, counterSame, forestSame, afterSafe, afterSlots, ?_, ?_⟩
  · intro uv known
    refine ⟨protects uv known, ?_⟩
    rw [forestSame, ownSame]
    exact fresh_avoids before.core safe.1 uv (slots.bounded uv known) tries
  · intro offset inside
    refine ⟨?_, ?_, ?_⟩
    · intro known
      have oldBound := slots.bounded (before.core.counter + offset) known
      omega
    · have values : after.core.values = before.core.values ++
          List.replicate tries.length (.unenumerated none []) := by
        rw [coreSame, suspension_values]
      have outside : before.core.values.length ≤ before.core.counter + offset := by
        rw [← safe.1.aligned]
        omega
      have difference : before.core.counter + offset - before.core.values.length = offset := by
        rw [← safe.1.aligned]
        omega
      rw [values, List.getElem?_append_right outside, difference]
      exact List.getElem?_replicate_of_lt inside
    · rw [forestSame]
      refine ⟨1, .root ?_⟩
      simp [UnionFind.read, outside_forest before.core.representatives before.core.counter
        (before.core.counter + offset) safe.1.forest (by omega)]

end MicroCFTA.SourceSynthesisProgramRolesClassAllocation
