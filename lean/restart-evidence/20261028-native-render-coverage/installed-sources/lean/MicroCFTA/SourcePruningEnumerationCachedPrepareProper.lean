import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.EnumerationProgress

/-!
# Proper pending paths in actual shallow child preparations

The ordinary branch stores its input bucket in a fresh slot.
Its actual preparation excludes terminal tries from that bucket.
Mu and Union allocate an empty bucket. Empty has no successful raw row.
Cached erasure identifies the same actual prepared core.
-/
namespace MicroCFTA.SourcePruningEnumerationShallowChild
open Fragments EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationProgress EnumerationSchedule
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every actual successful prepared action retains proper pending paths. -/
theorem prepared_proper
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard (Fragment Symbol)) (fragment : Fragment Symbol)
    (proper : ProperState before) (inputs : ProperInputs scs)
    (prepared : prepareChild scs value = some action)
    (success : Success action before fragment after) : ProperState after := by
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
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have payload : ProperValue (.unenumerated (some (entry.identity + 1)) scs : UVarValue Symbol) := by
          intro sc member
          refine ⟨(inputs sc member).1, (inputs sc member).2, ?_⟩
          exact Bool.eq_false_iff.mpr (fun tagged =>
            terminal (List.any_eq_true.mpr ⟨sc, member, tagged⟩))
        have writtenProperState := setValue_proper before.counter
          (.unenumerated (some (entry.identity + 1)) scs)
          (allocated (some (entry.identity + 1)) before) written
          (allocation_proper (some (entry.identity + 1)) before proper) payload writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        exact writtenProperState
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
        exact allocation_proper (some (entry.identity + 1)) before proper

end MicroCFTA.SourcePruningEnumerationShallowChild

namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open Fragments EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationProgress EnumerationSchedule
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every attached row retains proper paths at its actual successful raw core. -/
theorem rows_proper
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (rows : List (Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    (proper : ProperState before.core) (inputs : ProperInputs scs)
    (cached : prepareChild heap fuel scs value before = some rows) :
    ∀ fragment after, (fragment, after) ∈ rows → ProperState after.core := by
  have raw := erase_some heap fuel scs value before rows cached
  cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := EnumGuard) scs value with
  | none =>
      simp only [prepared, Option.map_none, reduceCtorEq] at raw
  | some action =>
      simp only [prepared, Option.map_some, Option.some.injEq] at raw
      intro fragment after member
      apply SourcePruningEnumerationShallowChild.prepared_proper scs value before.core after.core
        action fragment proper inputs prepared
      rw [Success, raw]
      exact List.mem_map.mpr ⟨(fragment, after), member, rfl⟩

/-- The actual candidate retains proper paths, including the unchanged rejection cache. -/
theorem cache_proper
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (proper : ProperState before.core) (inputs : ProperInputs scs)
    (observed : (match prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) : ProperState after.core := by
  cases prepared : prepareChild heap fuel scs value before with
  | none =>
      simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact proper
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              exact rows_proper heap fuel scs value before [(fragment, reached)]
                proper inputs prepared fragment reached (by simp)
          | cons row rest =>
              simp only [prepared, reduceCtorEq] at observed

end MicroCFTA.SourcePruningEnumerationCachedPrepare
