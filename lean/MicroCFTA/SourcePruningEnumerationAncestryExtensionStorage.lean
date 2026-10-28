import MicroCFTA.SourcePruningEnumerationAncestryExtension
import MicroCFTA.SourcePruningEnumerationCachedChild

/-!
# All-slot recursion ancestry through actual cached storage

Writes retain both ancestry fields.
Allocation retains old keys at every slot, including the fresh counter.
Ordinary preparation composes its actual allocation and bucket write.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeIndex
open EnumerationState SourcePruningEnumerationAncestryExtension
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual indexed write retains all recursion keys and the exact expansion history. -/
theorem write_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel target : Nat} {value : UVarValue Symbol} {gained lost : List Suspended}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    (observed : write heap fuel target value gained lost before = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  unfold write at observed
  obtain ⟨_flag, _classified, observed⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨_removed, _removedCounts, observed⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨_saved, _savedCounts, observed⟩ := Option.bind_eq_some_iff.mp observed
  cases observed
  exact ⟨fun _ _ member => member, rfl⟩

end MicroCFTA.SourcePruningEnumerationNativeIndex

namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState SourcePruningEnumerationAncestryExtension
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual allocation retains every old slot key, including old keys at its fresh counter. -/
theorem allocate_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol NativeGuard} {node : Option Nat}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard} {fresh : Nat}
    (observed : allocate heap node before = some (fresh, after)) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  unfold allocate at observed
  obtain ⟨_flag, _classified, same⟩ := Option.map_eq_some_iff.mp observed
  have coreSame : after.core = EnumerationState.allocated node before.core :=
    (congrArg (fun result : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard => result.2.core) same).symm
  rw [coreSame]
  exact ⟨Extends.allocated before.core node, rfl⟩

/-- The actual old-slot read and indexed replacement retain both ancestry fields. -/
theorem writeSlot_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel target : Nat} {value : UVarValue Symbol}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard}
    (observed : writeSlot heap fuel target value before = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  unfold writeSlot at observed
  obtain ⟨_old, _stored, written⟩ := Option.bind_eq_some_iff.mp observed
  exact SourcePruningEnumerationNativeIndex.write_ancestry_extension written

/-- An actual ordinary child preparation extends every slot and retains expansion ancestry. -/
theorem prepareOrdinary_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol NativeGuard}
    {fuel : Nat} {scs : List Suspended} {value : InternedConstructorTemplates.Value Symbol NativeGuard}
    {before after : EnumerationExpandableIndex.Cached Symbol EnumGuard} {fragment : Fragments.Fragment Symbol}
    (observed : prepareOrdinary heap fuel scs value before = some (fragment, after)) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  cases value with
  | empty | reference | union | mu => simp [prepareOrdinary] at observed
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareOrdinary, terminal] at observed
      · simp only [prepareOrdinary, ite_eq_right terminal] at observed
        obtain ⟨_handle, _encoded, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨allocation, allocated, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨_fresh, _middle⟩ := allocation
        obtain ⟨returned, written, same⟩ := Option.map_eq_some_iff.mp observed
        have allocatedFields := allocate_ancestry_extension allocated
        have writtenFields := writeSlot_ancestry_extension written
        have extended := allocatedFields.1.trans writtenFields.1
        have expansionSame := writtenFields.2.trans allocatedFields.2
        have cacheSame : returned = after := congrArg Prod.snd same
        simpa only [cacheSame] using And.intro extended expansionSame

end MicroCFTA.SourcePruningEnumerationCachedChild
