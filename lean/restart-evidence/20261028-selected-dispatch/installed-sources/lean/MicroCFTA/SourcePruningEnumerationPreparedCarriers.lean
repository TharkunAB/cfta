import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.EnumerationGraphReferences

/-!
# Graph carriers in actual native child preparation

Each successful prepared child allocates a native handle before returning its hole.
The ordinary branch retains that handle when it attaches inherited constraints.
Mu and Union retain their allocated handle with an empty suspended bucket.
Actual cached erasure exposes the same successful action and core.
-/
namespace MicroCFTA.SourcePruningEnumerationShallowChild
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationCarriers EnumerationGraphReferences InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem allocated_carriers (node : Nat) (before : EnumerationState.State Symbol EnumGuard)
    (safe : Safe before) (references : ReferencesCarry before) :
    PreservesCarriers before (allocated (some node) before) ∧
      ReferencesCarry (allocated (some node) before) ∧
      FragmentCarries (allocated (some node) before) (.hole before.counter) := by
  have preserved := allocation_carriers (some node) before
  refine ⟨preserved,
    references_transport before _ references preserved (allocation_origin (some node) before) rfl, ?_⟩
  apply fragmentCarries_hole
  exact carries_self (allocated (some node) before) safe.1.total before.counter
    (.unenumerated (some node) []) (allocated_slot (some node) before safe.1.aligned) trivial

/-- Every actual successful shallow row retains old carriers and supplies its returned hole. -/
theorem prepared_carriers
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard (Fragment Symbol)) (fragment : Fragment Symbol)
    (safe : Safe before) (references : ReferencesCarry before)
    (prepared : prepareChild scs value = some action)
    (success : Success action before fragment after) :
    PreservesCarriers before after ∧ ReferencesCarry after ∧ FragmentCarries after fragment := by
  cases value with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      exact (reject_unsuccessful before after fragment success).elim
  | reference name =>
      simp only [prepareChild, reduceCtorEq] at prepared
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have allocatedFacts := allocated_carriers (entry.identity + 1) before safe references
        have origin := setValue_origin before.counter
          (.unenumerated (some (entry.identity + 1)) scs)
          (allocated (some (entry.identity + 1)) before) written
          (by intro other impossible; cases impossible) writing
        have writtenSame := (EnumerationDriver.modify_success _ (allocated (some (entry.identity + 1)) before) written).mp writing
        have writtenCarriers : PreservesCarriers (allocated (some (entry.identity + 1)) before) written := by
          rw [writtenSame]
          exact set_graph_carriers _ before.counter (.unenumerated (some (entry.identity + 1)) scs) trivial
        have writtenReferences := references_transport _ written allocatedFacts.2.1
          writtenCarriers origin (by rw [writtenSame])
        obtain ⟨fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst fragment
        subst after
        exact ⟨allocatedFacts.1.trans writtenCarriers, writtenReferences,
          allocatedFacts.2.2.preserve _ writtenCarriers⟩
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst fragment
        subst after
        exact allocated_carriers (entry.identity + 1) before safe references

end MicroCFTA.SourcePruningEnumerationShallowChild

namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCarriers EnumerationGraphReferences InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Each actual cached row inherits carrier provenance from its exact erased native preparation. -/
theorem rows_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (rows : List (Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    (safe : Safe before.core) (references : ReferencesCarry before.core)
    (cached : prepareChild heap fuel scs value before = some rows) :
    ∀ fragment after, (fragment, after) ∈ rows →
      PreservesCarriers before.core after.core ∧ ReferencesCarry after.core ∧
        FragmentCarries after.core fragment := by
  have raw := erase_some heap fuel scs value before rows cached
  cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := EnumGuard) scs value with
  | none =>
      simp only [prepared, Option.map_none, reduceCtorEq] at raw
  | some action =>
      simp only [prepared, Option.map_some, Option.some.injEq] at raw
      intro fragment after member
      apply SourcePruningEnumerationShallowChild.prepared_carriers scs value before.core after.core
        action fragment safe references prepared
      rw [Success, raw]
      exact List.mem_map.mpr ⟨(fragment, after), member, rfl⟩

end MicroCFTA.SourcePruningEnumerationCachedPrepare
