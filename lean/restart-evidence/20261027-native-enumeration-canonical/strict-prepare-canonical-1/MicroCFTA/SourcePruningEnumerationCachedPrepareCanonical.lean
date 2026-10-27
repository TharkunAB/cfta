import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.EnumerationValidity

/-!
# Canonical tries in actual shallow child preparations

Ordinary children store the valid input bucket in a fresh slot.
Boundary children allocate an empty bucket. Empty rejects without a raw row.
The cache erasure receipt identifies the same successful raw and cached cores.
-/
namespace MicroCFTA.SourcePruningEnumerationShallowChild
open Fragments EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every actual successful prepared action retains canonical stored tries. -/
theorem prepared_canonical
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard (Fragment Symbol)) (fragment : Fragment Symbol)
    (canonical : Canonical before) (inputs : ValidSuspended scs)
    (prepared : prepareChild scs value = some action)
    (success : Success action before fragment after) : Canonical after := by
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
      · simp only [prepareChild, terminal, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have writtenCanonical := setValue_canonical before.counter
          (.unenumerated (some (entry.identity + 1)) scs)
          (allocated (some (entry.identity + 1)) before) written
          (allocation_canonical (some (entry.identity + 1)) before canonical) inputs writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        exact writtenCanonical
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
        exact allocation_canonical (some (entry.identity + 1)) before canonical

end MicroCFTA.SourcePruningEnumerationShallowChild

namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open Fragments EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every attached row cache is canonical at the same actual successful raw core. -/
theorem rows_canonical
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (rows : List (Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    (canonical : Canonical before.core) (inputs : ValidSuspended scs)
    (cached : prepareChild heap fuel scs value before = some rows) :
    ∀ fragment after, (fragment, after) ∈ rows → Canonical after.core := by
  have raw := erase_some heap fuel scs value before rows cached
  cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := EnumGuard) scs value with
  | none =>
      simp only [prepared, Option.map_none, reduceCtorEq] at raw
  | some action =>
      simp only [prepared, Option.map_some, Option.some.injEq] at raw
      intro fragment after member
      apply SourcePruningEnumerationShallowChild.prepared_canonical scs value before.core after.core
        action fragment canonical inputs prepared
      rw [Success, raw]
      exact List.mem_map.mpr ⟨(fragment, after), member, rfl⟩

/-- The actual nonterminal candidate retains canonical tries, including empty rejection. -/
theorem cache_canonical
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (canonical : Canonical before.core) (inputs : ValidSuspended scs)
    (observed : (match prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) : Canonical after.core := by
  cases prepared : prepareChild heap fuel scs value before with
  | none =>
      simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact canonical
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              exact rows_canonical heap fuel scs value before [(fragment, reached)]
                canonical inputs prepared fragment reached (by simp)
          | cons row rest =>
              simp only [prepared, reduceCtorEq] at observed

end MicroCFTA.SourcePruningEnumerationCachedPrepare
