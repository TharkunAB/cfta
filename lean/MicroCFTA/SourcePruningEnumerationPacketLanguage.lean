import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Assignment meaning of the restored captured cache

A native Post retains every realized handle of the captured cache.
The full returned packet and its assignment meaning use the same cache.
This law does not replace that cache with a preceding subtree's output.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- An actual native Post retains the whole captured packet and every complete assignment. -/
theorem captured_post_semantics
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory next : Inventory) (caller reached : Caller width) (memos final : Memos)
    (metadata : Metadata Typing) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (post : Post formulas solver next caller reached final) :
    Packet formulas solver next reached final metadata before ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        EnumerationCorrectness.Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient reached.checked.native.machine.heap) residualMeaning assignment before.core ↔
        EnumerationCorrectness.Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment before.core := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  refine ⟨captured_post packet post, ?_⟩
  intro ambient residualMeaning assignment
  exact SourcePruningEnumerationNativeLanguage.satisfies_keeps
    (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
    reached.checked.native.machine.heap before.core residualMeaning assignment realized post.effects.keeps

end MicroCFTA.SourcePruningEnumerationRecursive
