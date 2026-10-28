import MicroCFTA.SourcePruningEnumerationFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationHeadReceiptCarriers
import MicroCFTA.SourcePruningEnumerationCallbackCarriers
import MicroCFTA.SourcePruningEnumerationEntry

/-!
# Graph provenance at the actual ordinary hook input and callback

Entry retains values, residuals and graph-bearing equality classes.
The stable completed head supplies its own returned fragment carriers.
The actual callback record retains the same completed references.
-/
namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open EnumerationCarriers EnumerationGraphReferences
open EnumerationSemantics InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- Successful entry retains old carriers and stored references. -/
theorem enter_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (success : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after := by
  unfold enter at success
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  have readFrame := (getValue_frame fuel uv before read value total reading).1
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have compressedFrame := representative_frame fuel uv found read compressed (readFrame.total total) compressing
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
              exact ⟨compressedFrame.total (readFrame.total total),
                readFrame.carriers.trans compressedFrame.carriers,
                compressedFrame.references (readFrame.references references)⟩

end MicroCFTA.SourcePruningEnumerationEntry


namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame InternedConstructorTemplates
open EnumerationCarriers EnumerationGraphReferences
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
variable {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
variable {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
variable {returnedInventory : Inventory} {returnedMemos : Memos}

/-- Actual entry and its completed head retain carriers at their own cache. -/
theorem OrdinaryHistoryReceipt.carriers
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (references : ReferencesCarry before.core) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core ∧ FragmentCarries after.core fragment := by
  obtain ⟨entered, handle, scs, decoded, _edge, _headSeed, _inherited,
    _headInventory, _headCaller, _headMemos, _headBound,
    original, entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv)
      before.core (uv, handle, scs, decoded) entered.core := by
    rw [Success, entry]
    exact List.mem_singleton_self _
  have enteredFacts := SourcePruningEnumerationEntry.enter_carriers caller.checked.native.machine.heap
    workFuel uv before.core entered.core uv handle scs decoded original.safe.1.total references entrySuccess
  have completedFacts := completed.carriers enteredFacts.2.2
  exact ⟨completedFacts.1, enteredFacts.2.1.trans completedFacts.2.1, completedFacts.2.2⟩

/-- Either actual callback result retains the completed cache and fragment carriers. -/
theorem OrdinaryHistoryReceipt.carriers_after_callback
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (references : ReferencesCarry before.core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) :
    UnionFind.Total callbackCore.representatives ∧ PreservesCarriers before.core callbackCore ∧
      ReferencesCarry callbackCore ∧ FragmentCarries callbackCore fragment := by
  have completedFacts := receipt.carriers references
  have recordedFacts := SourcePruningRecordTypes.recordTypes_carriers graph templates callbackFuel metadata uv
    (.inl fragment) after.core callbackCore result completedFacts.1 completedFacts.2.2.1 recorded
  exact ⟨recordedFacts.1, completedFacts.2.1.trans recordedFacts.2.1, recordedFacts.2.2,
    completedFacts.2.2.2.preserve fragment recordedFacts.2.1⟩

end MicroCFTA.SourcePruningEnumerationRecursive
