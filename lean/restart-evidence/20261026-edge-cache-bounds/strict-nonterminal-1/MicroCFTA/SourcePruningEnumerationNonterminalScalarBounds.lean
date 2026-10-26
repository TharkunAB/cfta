import MicroCFTA.SourcePruningEnumerationNonterminalCacheBounds

/-!
# Scalar bounds without supply alignment

Allocation appends an empty bucket. A slot replacement adds at most
the new bucket length, even when the supply is not aligned.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open EnumerationState
open SourcePruningEnumerationNodes
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

private theorem sum_map_set_le {α : Type} (weight : α → Nat)
    (values : List α) (index : Nat) (value : α) :
    ((values.set index value).map weight).sum ≤ (values.map weight).sum + weight value := by
  induction values generalizing index with
  | nil => simp
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
          omega
      | succ index =>
          have bound := ih index
          simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
          omega

private theorem write_mass_le (before : Core) (target : Nat)
    (node : Option Nat) (scs : List Suspended) :
    suspendedBound {before with values := before.values.set target (.unenumerated node scs)} ≤
      suspendedBound before + scs.length := by
  simpa only [suspendedBound] using sum_map_set_le
    (fun value : UVarValue Symbol => match value with
      | .unenumerated _ bucket => bucket.length
      | _ => 0) before.values target (.unenumerated node scs)

/-- An actual singleton adds one slot and at most its incoming bucket length. -/
theorem singleton_counter_mass_bound
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List Suspended) (value : Node) (before after : Cached)
    (fragment : Fragments.Fragment Symbol)
    (cached : prepareChild heap fuel scs value before = some [(fragment, after)]) :
    after.core.counter = before.core.counter + 1 ∧
      suspendedBound after.core ≤ suspendedBound before.core + scs.length := by
  cases value with
  | empty => simp [prepareChild] at cached
  | reference name => simp [prepareChild] at cached
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareChild, SourcePruningEnumerationCachedChild.prepareOrdinary, terminal] at cached
      simp only [prepareChild, Option.map_eq_some_iff] at cached
      obtain ⟨result, prepared, rowsSame⟩ := cached
      have resultSame : result = (fragment, after) := (List.cons.inj rowsSame).1
      subst result
      simp only [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal, Bool.false_eq_true,
        ↓reduceIte, encodeNode, Option.bind_some, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at prepared
      obtain ⟨allocation, nativeAllocated, writtenAfter, written, pairSame⟩ := prepared
      have afterSame : writtenAfter = after := (Prod.mk.inj pairSame).2
      subst writtenAfter
      simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at nativeAllocated
      obtain ⟨flag, _classified, allocationSame⟩ := nativeAllocated
      subst allocation
      simp only [SourcePruningEnumerationCachedChild.writeSlot, Option.bind_eq_some_iff] at written
      obtain ⟨old, _stored, nativeWritten⟩ := written
      simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff,
        Option.some.injEq] at nativeWritten
      obtain ⟨afterFlag, _afterClassified, removed, _removedCounts, saved, _savedCounts, afterSame⟩ := nativeWritten
      subst after
      refine ⟨rfl, ?_⟩
      simpa only [allocated_mass] using
        write_mass_le (allocated (some (entry.identity + 1)) before.core)
          before.core.counter (some (entry.identity + 1)) scs
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareChild, terminal] at cached
      simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, encodeNode,
        Option.bind_some, Option.map_eq_some_iff] at cached
      obtain ⟨allocation, nativeAllocated, rowsSame⟩ := cached
      simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at nativeAllocated
      obtain ⟨flag, _classified, allocationSame⟩ := nativeAllocated
      subst allocation
      have afterSame := (Prod.mk.inj (List.cons.inj rowsSame).1).2
      subst after
      exact ⟨rfl, by rw [allocated_mass]; exact Nat.le_add_right _ _⟩

end MicroCFTA.SourcePruningEnumerationCachedPrepare
