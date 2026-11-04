import MicroCFTA.SourceCurrentPacketMuRun
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationSelectedPreparation

namespace MicroCFTA.SourceCurrentSelectedPreparationMuRun
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationObservation (PendingRealized)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
variable {Typing : Type} {width : Nat}

/-- Derive the actual selected Mu outcome from the original entry inputs. -/
theorem complete [DecidableEq (EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (memos : Memos)
    (metadata : Metadata Typing) (before : Cached) (uv handle : Nat)
    (scs : List EnumerationState.Suspended)
    (packet : SourcePruningEnumerationRecursive.Packet
      formulas solver inventory beforeCaller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∃ (entryFuel : Nat) (decoded : Node) (afterEntry : Cached),
      (∀ extra, ExceptT.run (SourcePruningEnumerationEntry.enter
        beforeCaller.checked.native.machine.heap (entryFuel + extra) uv before.core) =
        [.ok ((uv, handle, scs, decoded), afterEntry.core)]) ∧
      SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap handle =
        some decoded ∧
      Available beforeCaller.checked.native.machine.heap decoded ∧ decoded.free = [] ∧
      match decoded with
      | .mu entry body depth ordinary =>
          ∃ (result : Node) (nextHeap : InternedConstructorTemplates.State Symbol Constraint)
            (saved : Memos) (afterCaller : Caller width),
            InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memos.unfolding
              beforeCaller.checked.native.machine.heap = .done (result, saved.unfolding) nextHeap ∧
            InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
              beforeCaller.checked.native.machine.heap = .done result nextHeap ∧
            afterCaller = SourceCurrentAllocatedPartialState.advance beforeCaller
              (advancePhysical beforeCaller.checked ⟨nextHeap, beforeCaller.checked.operations⟩)
              beforeCaller.fourth beforeCaller.merge ∧
            Post formulas solver inventory beforeCaller afterCaller saved ∧
            saved.query = memos.query ∧ Cache.Extends memos.unfolding saved.unfolding ∧
            Available nextHeap result ∧ result.free = [] ∧
            (∀ (holds : Constraint → Language.Term Symbol → Bool)
              (ambient : InternedGuardedLanguage.Env Symbol) (term : Language.Term Symbol),
              InternedGuardedLanguage.meaning holds ambient result term ↔
                InternedGuardedLanguage.meaning holds ambient (.mu entry body depth ordinary) term) ∧
            PendingRealized nextHeap before.core ∧
            (∀ nativeFuel, SourcePruningEnumerationSelectedValue.run nativeFuel
              (.mu entry body depth ordinary) beforeCaller.checked.native.machine.heap =
                .done result nextHeap) ∧
            (∀ extra nativeFuel, SourcePruningEnumerationSelectedPreparation.run
              (entryFuel + extra) nativeFuel uv beforeCaller before =
              ([.ok ((uv, handle, scs, .mu entry body depth ordinary), afterEntry.core)],
                some (.done result nextHeap))) ∧
            (∀ limit, InternedMuDepthInventory.Bounded beforeCaller.checked.native.machine.heap limit →
              InternedMuDepthInventory.Bounded nextHeap limit)
      | _ => True := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨entryFuel, decoded, afterEntry, entryRun, lookup, available, closed, _entryRest⟩ :=
    SourcePruningEnumerationSelectedEntry.complete beforeCaller.checked.native.machine.heap
      before uv handle scs roots ready stored realized paths counts flags
  refine ⟨entryFuel, decoded, afterEntry, entryRun, lookup, available, closed, ?_⟩
  cases decoded with
  | empty => exact True.intro
  | reference _name => exact True.intro
  | node _entry _edges _depth _free => exact True.intro
  | union _entry _members _depth _free => exact True.intro
  | mu entry body depth ordinary =>
      obtain ⟨result, nextHeap, saved, afterCaller, memoRun, unfoldRun, callerEq, post,
        queryEq, unfoldingExtends, resultAvailable, resultClosed, meaning, nextRealized,
        runAll, bounded⟩ := SourceCurrentPacketMuRun.complete formulas solver inventory
          beforeCaller memos metadata before entry body depth ordinary packet available closed
      refine ⟨result, nextHeap, saved, afterCaller, memoRun, unfoldRun, callerEq, post,
        queryEq, unfoldingExtends, resultAvailable, resultClosed, meaning, nextRealized,
        runAll, ?_, bounded⟩
      intro extra nativeFuel
      simp only [SourcePruningEnumerationSelectedPreparation.run, entryRun extra, runAll nativeFuel]

end MicroCFTA.SourceCurrentSelectedPreparationMuRun
