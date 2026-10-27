import MicroCFTA.SourcePruningEnumerationFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationHeadReceiptProper
import MicroCFTA.SourcePruningEnumerationEntry
import MicroCFTA.EnumerationProgress

/-!
# Proper storage at the actual ordinary hook input and callback

Actual entry and the retained completed head use the same current cache.
Either actual callback result retains the completed stored values.
No arbitrary hook or later recursive execution is a premise.
-/
namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationProgress
open EnumerationSemantics InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- Successful entry retains proper storage. -/
theorem enter_proper
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (proper : ProperState before)
    (success : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    ProperState after := by
  unfold enter at success
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readProper, _storedProper⟩ := getValue_proper fuel uv before read value proper reading
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have compressedProper := representative_proper fuel uv found read compressed readProper compressing
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
              exact compressedProper

end MicroCFTA.SourcePruningEnumerationEntry


namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationProgress InternedConstructorTemplates
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

/-- Actual entry and its completed head preserve proper storage. -/
theorem OrdinaryHistoryReceipt.proper
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (proper : ProperState before.core) : ProperState after.core := by
  obtain ⟨entered, handle, scs, decoded, _edge, _headSeed, _inherited,
    _headInventory, _headCaller, _headMemos, _headBound,
    _original, entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv)
      before.core (uv, handle, scs, decoded) entered.core := by
    rw [Success, entry]
    exact List.mem_singleton_self _
  have enteredProper := SourcePruningEnumerationEntry.enter_proper caller.checked.native.machine.heap
    workFuel uv before.core entered.core uv handle scs decoded proper entrySuccess
  exact completed.proper enteredProper

/-- Either actual callback result preserves the same completed proper storage. -/
theorem OrdinaryHistoryReceipt.proper_after_callback
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (proper : ProperState before.core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) : ProperState callbackCore := by
  have completedProper := receipt.proper proper
  obtain ⟨_entered, _handle, _scs, _decoded, _edge, _headSeed, _inherited,
    _headInventory, _headCaller, _headMemos, _headBound,
    _original, _entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have frame := SourcePruningRecordTypes.recordTypes_frame graph templates callbackFuel metadata uv
    (.inl fragment) after.core callbackCore result completed.completed.safe.1.total recorded
  intro value member
  exact completedProper value (by simpa only [frame.values] using member)

end MicroCFTA.SourcePruningEnumerationRecursive
