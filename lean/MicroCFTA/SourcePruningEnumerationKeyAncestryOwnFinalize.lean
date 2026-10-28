import MicroCFTA.SourcePruningEnumerationKeyAncestryStorage
import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.SourcePruningEnumerationSelectedEdge

/-!
# Finite historical key shapes through own classes and finalization

Each own-class allocation inherits only the existing key shapes.
Finalization clears expansion ancestry and retains the slot histories.
Residual recording does not add historical keys.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual own-class allocation preserves the original history carrier. -/
theorem suspendMany_key_ancestry
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    {carrier : List (List (List (List Nat)))}
    (bounded : KeyAncestry carrier before.core)
    (observed : suspendMany heap tries before = some (suspended, after)) :
    KeyAncestry carrier after.core := by
  induction tries generalizing before after suspended with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have cacheSame : before = after := congrArg Prod.snd same
      simpa only [cacheSame] using bounded
  | cons trie rest ih =>
      simp only [suspendMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocated, result, continued, same⟩ := observed
      have allocationBounded := SourcePruningEnumerationCachedChild.allocate_key_ancestry bounded allocated
      have resultBounded := ih allocation.2 result.2 result.1 allocationBounded continued
      have cacheSame : result.2 = after := congrArg Prod.snd same
      simpa only [cacheSame] using resultBounded

local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- Each actual prepared own-class row retains the original historical key shapes. -/
theorem prepare_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {heap : InternedConstructorTemplates.State Symbol Constraint}
    {scs : List Suspended} {edge : InternedConstructorTemplates.EdgeValue Symbol Constraint}
    {before : Cached} {rows : List _}
    (bounded : KeyAncestry carrier before.core)
    (observed : prepare heap scs edge before = some rows) :
    ∀ row ∈ rows, KeyAncestry carrier row.2.core := by
  unfold prepare at observed
  split at observed
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [projected] at observed
        cases observed
    | some projection =>
        obtain ⟨tries, residual⟩ := projection
        simp only [projected] at observed
        obtain ⟨result, suspended, same⟩ := Option.map_eq_some_iff.mp observed
        have resultBounded := suspendMany_key_ancestry heap tries before result.2 result.1 bounded suspended
        intro row member
        rw [← same] at member
        have rowSame := List.mem_singleton.mp member
        cases rowSame
        exact resultBounded
  · have rowsSame : [] = rows := Option.some.inj observed
    rw [← rowsSame]
    intro row member
    cases member

end MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual captured finalization retains the carrier after clearing expansion ancestry. -/
theorem run_key_ancestry
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    {carrier : List (List (List (List Nat)))}
    (bounded : KeyAncestry carrier before.core)
    (observed : run heap fuel target fragment before = some after) :
    KeyAncestry carrier after.core := by
  unfold run at observed
  obtain ⟨_old, _stored, written⟩ := Option.bind_eq_some_iff.mp observed
  apply SourcePruningEnumerationNativeIndex.write_key_ancestry _ written
  exact ⟨bounded.1, by intro key member; cases member⟩

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual completed-edge residual recording retains both historical key fields. -/
theorem finish_key_ancestry
    (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    {carrier : List (List (List (List Nat)))}
    (bounded : KeyAncestry carrier before.core) :
    KeyAncestry carrier (finish residual fragment before).core := bounded

end MicroCFTA.SourcePruningEnumerationSelectedEdge
