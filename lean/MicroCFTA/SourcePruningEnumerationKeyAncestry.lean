import MicroCFTA.SourcePruningEnumerationModelKeyShapes
import MicroCFTA.SourcePruningEnumerationEntry
import MicroCFTA.SourcePruningEnumerationCachedChild

/-!
# Original finite trie-list shapes in actual ancestry storage

The carrier bounds the whole trie list of each historical key.
It does not bound the key's native handle.
The invariant covers every slot, including slots beyond the current counter.
Allocation inherits the old ancestry at its fresh counter.
-/
namespace MicroCFTA.SourcePruningEnumerationKeyAncestry
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
variable {Symbol Guard : Type}

/-- Every stored ancestry key uses a whole trie-list shape from the fixed carrier. -/
def KeyAncestry (carrier : List (List (List (List Nat)))) (state : State Symbol Guard) : Prop :=
  (∀ slot key, key ∈ state.recursionAncestry slot → key.tries ∈ carrier) ∧
    ∀ key, key ∈ state.expansionAncestry → key.tries ∈ carrier

/-- Literal startup has no historical keys at any slot. -/
theorem KeyAncestry.initial (carrier : List (List (List (List Nat)))) (root : Nat) :
    KeyAncestry carrier (initial root : State Symbol Guard) := by
  constructor
  · intro slot key member
    cases member
  · intro key member
    cases member

/-- Complete compression frames retain the same historical key carrier. -/
theorem KeyAncestry.frame {carrier : List (List (List (List Nat)))}
    {before after : State Symbol Guard} (bounded : KeyAncestry carrier before)
    (framed : Frame before after) : KeyAncestry carrier after := by
  constructor
  · intro slot key member
    exact bounded.1 slot key (by simpa only [framed.recursionAncestry] using member)
  · intro key member
    exact bounded.2 key (by simpa only [framed.expansionAncestry] using member)

/-- Actual allocation inherits only current expansion keys and old slot keys. -/
theorem KeyAncestry.allocated {carrier : List (List (List (List Nat)))}
    {state : State Symbol Guard} (bounded : KeyAncestry carrier state) (node : Option Nat) :
    KeyAncestry carrier (EnumerationState.allocated node state) := by
  refine ⟨?_, bounded.2⟩
  intro slot key member
  change key ∈ (if slot = state.counter then
    (state.expansionAncestry ++ state.recursionAncestry state.counter).eraseDups
    else state.recursionAncestry slot) at member
  by_cases fresh : slot = state.counter
  · simp only [ite_eq_left fresh, List.mem_eraseDups, List.mem_append] at member
    exact member.elim (bounded.2 key) (bounded.1 state.counter key)
  · exact bounded.1 slot key (by simpa only [ite_eq_right fresh] using member)

/-- Actual assimilation only combines two old key lists. -/
theorem KeyAncestry.assimilated {carrier : List (List (List (List Nat)))}
    {state : State Symbol Guard} (bounded : KeyAncestry carrier state)
    (target source : Nat) (merged : UVarValue Symbol) :
    KeyAncestry carrier (EnumerationCorrectness.assimilated state target source merged) := by
  refine ⟨?_, bounded.2⟩
  intro slot key member
  change key ∈ (if slot = target then
    (state.recursionAncestry source ++ state.recursionAncestry target).eraseDups
    else state.recursionAncestry slot) at member
  by_cases same : slot = target
  · simp only [ite_eq_left same, List.mem_eraseDups, List.mem_append] at member
    exact member.elim (bounded.1 source key) (bounded.1 target key)
  · exact bounded.1 slot key (by simpa only [ite_eq_right same] using member)

end MicroCFTA.SourcePruningEnumerationKeyAncestry

namespace MicroCFTA.SourcePruningEnumerationEntry
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationValidity
open EnumerationSemantics InternedConstructorTemplates
open SourcePruningEnumerationOrigins SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- Original input models derive the new key shape at an actual successful entry. -/
theorem enter_key_ancestry
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before)
    (origins : AssignmentOrigins whole before.counter assignment)
    (canonical : Canonical before) (aligned : before.counter = before.values.length)
    (bounded : KeyAncestry (SourcePruningEnumerationModelKeyShapes.keyShapes whole) before)
    (success : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    KeyAncestry (SourcePruningEnumerationModelKeyShapes.keyShapes whole) after := by
  unfold enter at success
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readFound, _lookup, stored, readSame⟩ :=
    (getValue_success fuel uv before read value).mp reading
  have readBounded : KeyAncestry (SourcePruningEnumerationModelKeyShapes.keyShapes whole) read := by
    rw [readSame]
    exact bounded
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          have inside : readFound.representative < before.counter := by
            rw [aligned]
            exact (List.getElem?_eq_some_iff.mp stored).1
          have inserted := SourcePruningEnumerationModelKeyShapes.stored_recursion_key_mem
            language meaning before whole assignment satisfied origins canonical inside stored
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨_resolved, _resolving, _sameRoot, compressedSame⟩ :=
            (representative_success fuel uv read compressed found).mp compressing
          have compressedBounded : KeyAncestry
              (SourcePruningEnumerationModelKeyShapes.keyShapes whole) compressed := by
            rw [compressedSame]
            exact readBounded
          cases lookup : SourcePruningEnumerationNodes.lookupNode heap storedHandle with
          | none =>
              simp only [lookup] at continued
              exact (success_failure .unresolvedReference compressed after _ continued).elim
          | some actual =>
              simp only [lookup] at continued
              obtain ⟨ignored, entered, modifying, final⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
              obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
              refine ⟨compressedBounded.1, ?_⟩
              intro key member
              change key ∈ (if MergedOrdinaryHeight.recursiveBoundary actual then
                (recursionKey storedHandle scs :: compressed.recursionAncestry found).eraseDups
                else compressed.recursionAncestry found) at member
              by_cases boundary : MergedOrdinaryHeight.recursiveBoundary actual = true
              · simp only [ite_eq_left boundary, List.mem_eraseDups, List.mem_cons] at member
                rcases member with same | old
                · subst key
                  exact inserted
                · exact compressedBounded.1 found key old
              · exact compressedBounded.1 found key (by
                  simpa only [ite_eq_right boundary] using member)

end MicroCFTA.SourcePruningEnumerationEntry

namespace MicroCFTA.SourcePruningEnumerationCachedChild
open SourcePruningEnumerationKeyAncestry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual cached allocation inherits only shapes from the original history domain. -/
theorem allocate_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {heap : InternedConstructorTemplates.State Symbol NativeGuard} {node : Option Nat}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard} {fresh : Nat}
    (bounded : KeyAncestry carrier before.core)
    (observed : allocate heap node before = some (fresh, after)) :
    KeyAncestry carrier after.core := by
  unfold allocate at observed
  obtain ⟨_flag, _classified, same⟩ := Option.map_eq_some_iff.mp observed
  have coreSame : after.core = EnumerationState.allocated node before.core :=
    (congrArg (fun result : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard => result.2.core) same).symm
  rw [coreSame]
  exact bounded.allocated node

end MicroCFTA.SourcePruningEnumerationCachedChild
