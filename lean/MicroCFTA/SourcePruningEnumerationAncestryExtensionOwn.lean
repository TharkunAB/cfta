import MicroCFTA.SourcePruningEnumerationAncestryExtensionStorage
import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.SourcePruningEnumerationSelectedEdge

/-!
# All-slot ancestry through actual own and shallow child preparation

Each returned preparation row extends the original slot histories.
Own and child preparation retain the exact expansion history.
Finalization retains slot histories and clears expansion ancestry.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState SourcePruningEnumerationAncestryExtension
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual own allocation retains every old slot key and the exact expansion history. -/
theorem suspendMany_ancestry_extension
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    (observed : suspendMany heap tries before = some (suspended, after)) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  induction tries generalizing before after suspended with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have cacheSame : before = after := congrArg Prod.snd same
      subst after
      exact ⟨Extends.refl before.core, rfl⟩
  | cons trie rest ih =>
      simp only [suspendMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocated, result, continued, same⟩ := observed
      have allocationFields := SourcePruningEnumerationCachedChild.allocate_ancestry_extension allocated
      have resultFields := ih allocation.2 result.2 result.1 continued
      have combined := And.intro (allocationFields.1.trans resultFields.1)
        (resultFields.2.trans allocationFields.2)
      have cacheSame : result.2 = after := congrArg Prod.snd same
      simpa only [cacheSame] using combined

local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- Each actual own-class row extends the input and retains its expansion history. -/
theorem prepare_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol Constraint}
    {scs : List Suspended} {edge : InternedConstructorTemplates.EdgeValue Symbol Constraint}
    {before : Cached} {rows : List _}
    (observed : prepare heap scs edge before = some rows) :
    ∀ row ∈ rows, Extends before.core row.2.core ∧
      row.2.core.expansionAncestry = before.core.expansionAncestry := by
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
        have resultFields := suspendMany_ancestry_extension heap tries before result.2 result.1 suspended
        intro row member
        rw [← same] at member
        have rowSame := List.mem_singleton.mp member
        cases rowSame
        exact resultFields
  · have rowsSame : [] = rows := Option.some.inj observed
    rw [← rowsSame]
    intro row member
    cases member

end MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open EnumerationState SourcePruningEnumerationAncestryExtension
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every actual shallow child row extends all slot histories and retains expansion ancestry. -/
theorem rows_ancestry_extension
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    (observed : prepareChild heap fuel scs value before = some rows) :
    ∀ fragment after, (fragment, after) ∈ rows → Extends before.core after.core ∧
      after.core.expansionAncestry = before.core.expansionAncestry := by
  cases value with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at observed
      subst rows
      intro fragment after member
      cases member
  | reference => simp [prepareChild] at observed
  | node entry edges depth free =>
      simp only [prepareChild, Option.map_eq_some_iff] at observed
      obtain ⟨result, prepared, rowsSame⟩ := observed
      subst rows
      intro fragment after member
      have same : after = result.2 := congrArg Prod.snd (List.mem_singleton.mp member)
      rw [same]
      exact SourcePruningEnumerationCachedChild.prepareOrdinary_ancestry_extension prepared
  | union entry members depth free | mu entry members depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareChild, terminal] at observed
      · simp only [prepareChild, ite_eq_right terminal] at observed
        obtain ⟨_handle, _encoded, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨allocation, allocated, rowsSame⟩ := Option.map_eq_some_iff.mp observed
        subst rows
        intro fragment after member
        have same : after = allocation.2 := congrArg Prod.snd (List.mem_singleton.mp member)
        rw [same]
        exact SourcePruningEnumerationCachedChild.allocate_ancestry_extension allocated

/-- The actual shallow cache extraction retains the relation, including Empty rejection. -/
theorem cache_ancestry_extension
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : (match prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  cases prepared : prepareChild heap fuel scs value before with
  | none => simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact ⟨Extends.refl before.core, rfl⟩
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              exact rows_ancestry_extension heap fuel scs value before [(fragment, reached)]
                prepared fragment reached (by simp)
          | cons row rest => simp only [prepared, reduceCtorEq] at observed

end MicroCFTA.SourcePruningEnumerationCachedPrepare

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState SourcePruningEnumerationAncestryExtension
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual finalization extends every slot's history and clears expansion ancestry. -/
theorem run_ancestry_extension
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : run heap fuel target fragment before = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = [] := by
  unfold run at observed
  obtain ⟨_old, _stored, written⟩ := Option.bind_eq_some_iff.mp observed
  have fields := SourcePruningEnumerationNativeIndex.write_ancestry_extension written
  exact ⟨fun slot key member => fields.1 slot key member, fields.2⟩

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open SourcePruningEnumerationAncestryExtension
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Residual recording retains every slot key and the exact expansion history. -/
theorem finish_ancestry_extension
    (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    Extends before.core (finish residual fragment before).core ∧
      (finish residual fragment before).core.expansionAncestry = before.core.expansionAncestry :=
  ⟨fun _ _ member => member, rfl⟩

end MicroCFTA.SourcePruningEnumerationSelectedEdge
