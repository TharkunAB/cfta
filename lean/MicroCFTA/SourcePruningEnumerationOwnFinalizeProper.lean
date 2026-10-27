import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.EnumerationProgress

/-!
# Proper pending paths at actual own-class and finalization receipts

Own-class allocation stores empty buckets.
Finalization replaces one stored bucket by an enumerated fragment.
Residual recording keeps all stored values.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationProgress EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- A successful native allocation stores an empty proper bucket. -/
theorem allocate_proper
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (node : Option Nat)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (uv : Nat)
    (proper : ProperState before.core)
    (observed : allocate heap node before = some (uv, after)) : ProperState after.core := by
  simp only [allocate, Option.map_eq_some_iff] at observed
  obtain ⟨flag, _classified, same⟩ := observed
  have coreSame : allocated node before.core = after.core := congrArg (fun result => result.2.core) same
  rw [← coreSame]
  exact allocation_proper node before.core proper

end MicroCFTA.SourcePruningEnumerationCachedChild

namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationProgress EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual own-class suspension preserves proper pending paths. -/
theorem suspendMany_proper
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    (proper : ProperState before.core)
    (observed : suspendMany heap tries before = some (suspended, after)) : ProperState after.core := by
  induction tries generalizing before after suspended with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have cacheSame : before = after := congrArg Prod.snd same
      simpa only [cacheSame] using proper
  | cons trie rest ih =>
      simp only [suspendMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocated, result, continued, same⟩ := observed
      have allocationProperState := SourcePruningEnumerationCachedChild.allocate_proper
        heap none before allocation.2 allocation.1 proper allocated
      have resultProperState := ih allocation.2 result.2 result.1 allocationProperState continued
      have cacheSame : result.2 = after := congrArg Prod.snd same
      simpa only [cacheSame] using resultProperState

end MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationProgress EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- The exact final captured-slot write preserves proper pending paths. -/
theorem written_proper
    (before after : EnumerationState.State Symbol EnumGuard) (target : Nat) (fragment : Fragments.Fragment Symbol)
    (proper : ProperState before)
    (written : after = {before with
      values := before.values.set target (.enumerated fragment)
      expansionAncestry := []}) : ProperState after := by
  subst after
  intro value member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact proper value old
  · subst value
    trivial

/-- Every actual indexed finalization cache has proper pending paths. -/
theorem run_proper
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (proper : ProperState before.core)
    (observed : run heap fuel target fragment before = some after) : ProperState after.core := by
  simp only [run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  exact written_proper before.core _ target fragment proper rfl

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Recording an actual completed edge residual keeps all proper pending paths. -/
theorem finish_proper (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (proper : ProperState before.core) :
    ProperState (finish residual fragment before).core := proper

end MicroCFTA.SourcePruningEnumerationSelectedEdge
