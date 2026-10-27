import MicroCFTA.SourcePruningEnumerationIsolatedPending
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationRestart

/-!
# Native boundary exclusion at the actual restart cache

An isolated pending native boundary has an exact false candidate flag.
An actual restart expansion therefore selects a different variable.
The native context is not used to infer validity of removed constraints.
-/
namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard NativeGuard : Type}

/-- The exact native candidate flag disables an isolated recursive boundary. -/
theorem IsolatedPending.disabled
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) (held handle : Nat)
    (value : Value Symbol NativeGuard)
    (isolated : IsolatedPending held handle before.core)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    before.expandable held = false := by
  simpa [SourcePruningEnumerationNativeIndex.candidate, isolated.stored, decoded, boundary]
    using (flags held).symm

/-- An actual pure selection cannot select the disabled isolated boundary. -/
theorem IsolatedPending.selected_ne
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) (held handle : Nat)
    (value : Value Symbol NativeGuard) (preference : List Nat → Option Nat) (uv : Nat)
    (isolated : IsolatedPending held handle before.core)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv) : uv ≠ held := by
  intro same
  subst uv
  have enabled := (SourcePruningEnumerationSelection.offered before preference held selected).2.1
  have disabled := isolated.disabled heap before held handle value decoded boundary flags
  rw [disabled] at enabled
  cases enabled

section Packet
open SourcePruningEnumerationRecursive
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The original packet realizes the same isolated handle and disables its exact candidate. -/
theorem packet_isolated_boundary
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (held handle : Nat)
    (value : Value Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (isolated : IsolatedPending held handle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    InternedProbeProvenance.Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
      before.expandable held = false := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, flags⟩ := packet.valid
  obtain ⟨actual, actualDecoded, available, closed⟩ := realized held handle [] isolated.stored
  have same : actual = value := Option.some.inj (actualDecoded.symm.trans decoded)
  subst actual
  exact ⟨available, closed,
    isolated.disabled caller.checked.native.machine.heap before held handle value decoded boundary flags⟩

/-- The actual restart gate at the original packet cannot select the isolated boundary. -/
theorem packet_restart_ne
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (held handle uv : Nat) (value : Value Symbol Constraint)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (isolated : IsolatedPending held handle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    uv ≠ held := by
  have selected : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨_roots, _paths, _storage, _realized, _counts, flags⟩ := packet.valid
  exact isolated.selected_ne caller.checked.native.machine.heap before held handle value (order metadata) uv
    decoded boundary flags selected

end Packet
end MicroCFTA.EnumerationDischargeHistory
