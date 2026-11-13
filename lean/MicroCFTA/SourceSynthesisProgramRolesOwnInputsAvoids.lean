import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.SourceSynthesisProgramRolesClassAllocation

/-!
# Program roles through actual own-class child preparation

The existing child-input producer runs once and retains its full receipt.
Current bucket separation protects every marked Program root.
The same own-class allocation retains the old mark set.
Every actual returned child bucket avoids each marked class.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesOwnInputsAvoids
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open SourcePruningEnumerationObservation
open InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
open SourcePruningEnumerationEdgeInputs (children)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol

/-- One actual own-class prefix retains all current Program slots and child separation. -/
theorem complete_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (parentAvailable : Available heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (before : Cached) (safe : Safe before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (slots : ProgramSlots valid literal heap before.core marked)
    (avoids : ∀ held, marked held → Avoids before.core.representatives held scs) :
    ∃ (action : EnumerateM Symbol Constraint
        (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint))
      (after : Cached),
      SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
      SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
        some [((edge.entry.key.symbol,
          (children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), after)] ∧
      ExceptT.run (action before.core) =
        [.ok ((edge.entry.key.symbol,
          (children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), after.core)] ∧
      after.core = suspendedState tries.length before.core ∧
      after.core.counter = before.core.counter + tries.length ∧
      after.core.representatives = before.core.representatives ∧
      Safe after.core ∧ Roots after.core.representatives roots ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      InputsPending after.core (scs ++ suspendedVars before.core.counter tries) ∧
      (∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
        Available heap incoming ∧ incoming.free = [] ∧
        (∀ sc ∈ bucket, sc.var < after.core.counter) ∧ InputsPending after.core bucket) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs →
        EnumerationDriver.Protected held before.core after.core ∧
          ∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
            Avoids after.core.representatives held bucket) ∧
      ProgramSlots valid literal heap after.core marked ∧
      ∀ held, marked held → EnumerationDriver.Protected held before.core after.core ∧
        ∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
          Avoids after.core.representatives held bucket := by
  obtain ⟨action, after, prepared, cachedRun, raw, coreSame, counter, forestSame,
      afterSafe, afterPaths, afterRealized, afterCounts, afterFlags, combinedPending,
      admitted, oldProtection⟩ :=
    SourcePruningEnumerationEdgeInputs.complete heap parentEntry edges depth free edge scs roots
      ready parentAvailable parentClosed selected before safe realized paths counts flags
      bounded pending allowed tries residual projected
  have observed := cachedRun
  simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
    projected, Option.map_eq_some_iff] at observed
  obtain ⟨allocation, ownRun, endpoints⟩ := observed
  have sameAfter : allocation.2 = after := (Prod.mk.inj (List.cons.inj endpoints).1).2
  have ownObserved : SourcePruningEnumerationCachedOwn.suspendMany heap tries before =
      some (allocation.1, after) := by
    rw [← sameAfter]
    exact ownRun
  obtain ⟨_ownSame, _cacheSame, _ownRaw, _counter, _forest, _safe, afterSlots,
      _oldProtection, _fresh⟩ :=
    SourceSynthesisProgramRolesClassAllocation.suspendMany_program_slots valid literal
      heap tries before after allocation.1 marked safe slots ownObserved
  refine ⟨action, after, prepared, cachedRun, raw, coreSame, counter, forestSame,
    afterSafe, afterPaths, afterRealized, afterCounts, afterFlags, combinedPending,
    admitted, oldProtection, afterSlots, ?_⟩
  intro held known
  exact oldProtection held (slots.bounded held known) (slots.roots held known) (avoids held known)

end MicroCFTA.SourceSynthesisProgramRolesOwnInputsAvoids
