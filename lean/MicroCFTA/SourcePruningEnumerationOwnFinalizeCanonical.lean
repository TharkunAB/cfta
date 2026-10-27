import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.EnumerationValidity

/-!
# Canonical tries at actual own-class and finalization receipts

Own-class allocation adds empty stored buckets.
Finalization replaces the captured bucket by a fragment.
Residual recording changes no stored trie.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- A successful native allocation stores an empty canonical bucket. -/
theorem allocate_canonical
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (node : Option Nat)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (uv : Nat)
    (canonical : Canonical before.core)
    (observed : allocate heap node before = some (uv, after)) : Canonical after.core := by
  simp only [allocate, Option.map_eq_some_iff] at observed
  obtain ⟨flag, _classified, same⟩ := observed
  have coreSame : allocated node before.core = after.core := congrArg (fun result => result.2.core) same
  rw [← coreSame]
  exact allocation_canonical node before.core canonical

end MicroCFTA.SourcePruningEnumerationCachedChild

namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual own-class suspension preserves canonical stored tries. -/
theorem suspendMany_canonical
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    (canonical : Canonical before.core)
    (observed : suspendMany heap tries before = some (suspended, after)) : Canonical after.core := by
  induction tries generalizing before after suspended with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have cacheSame : before = after := congrArg Prod.snd same
      simpa only [cacheSame] using canonical
  | cons trie rest ih =>
      simp only [suspendMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocated, result, continued, same⟩ := observed
      have allocationCanonical := SourcePruningEnumerationCachedChild.allocate_canonical
        heap none before allocation.2 allocation.1 canonical allocated
      have resultCanonical := ih allocation.2 result.2 result.1 allocationCanonical continued
      have cacheSame : result.2 = after := congrArg Prod.snd same
      simpa only [cacheSame] using resultCanonical

end MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- The exact final captured-slot write preserves canonical stored tries. -/
theorem written_canonical
    (before after : EnumerationState.State Symbol EnumGuard) (target : Nat) (fragment : Fragments.Fragment Symbol)
    (canonical : Canonical before)
    (written : after = {before with
      values := before.values.set target (.enumerated fragment)
      expansionAncestry := []}) : Canonical after := by
  subst after
  exact set_canonical target (.enumerated fragment) before canonical
    (by simp only [references, ValidSuspended, List.not_mem_nil, false_implies, implies_true])

/-- Every actual indexed finalization cache has canonical stored tries. -/
theorem run_canonical
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (canonical : Canonical before.core)
    (observed : run heap fuel target fragment before = some after) : Canonical after.core := by
  simp only [run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  exact set_canonical target (.enumerated fragment) _ canonical
    (by simp only [references, ValidSuspended, List.not_mem_nil, false_implies, implies_true])

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationValidity
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Recording an actual completed edge residual leaves canonical stored tries unchanged. -/
theorem finish_canonical (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (canonical : Canonical before.core) :
    Canonical (finish residual fragment before).core := canonical

end MicroCFTA.SourcePruningEnumerationSelectedEdge
