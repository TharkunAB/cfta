import MicroCFTA.SourcePruningEnumerationMu
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationSelectedValueMuDepth

namespace MicroCFTA.SourceCurrentPacketMuRun
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

/-- The selected Mu operation keeps the native postconditions and every original degree bound. -/
theorem complete [DecidableEq (EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (memos : Memos)
    (metadata : Metadata Typing) (before : Cached)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Node)
    (packet : SourcePruningEnumerationRecursive.Packet
      formulas solver inventory beforeCaller memos metadata before)
    (available : Available beforeCaller.checked.native.machine.heap (.mu entry body depth ordinary))
    (closed : (Value.mu entry body depth ordinary).free = []) :
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
      (∀ limit, InternedMuDepthInventory.Bounded beforeCaller.checked.native.machine.heap limit →
        InternedMuDepthInventory.Bounded nextHeap limit) := by
  have realized : PendingRealized beforeCaller.checked.native.machine.heap before.core := by
    obtain ⟨_, _, _, realized, _, _⟩ := packet.valid
    exact realized
  obtain ⟨result, nextHeap, saved, afterCaller, memoRun, unfoldRun, callerEq, post,
      queryEq, unfoldingExtends, resultAvailable, resultClosed, meaning, nextRealized⟩ :=
    SourcePruningEnumerationMu.complete formulas solver inventory beforeCaller memos
      entry body depth ordinary before.core packet.context available closed realized
  have runAll : ∀ nativeFuel, SourcePruningEnumerationSelectedValue.run nativeFuel
      (.mu entry body depth ordinary) beforeCaller.checked.native.machine.heap =
        .done result nextHeap := by
    intro nativeFuel
    simp only [SourcePruningEnumerationSelectedValue.run, unfoldRun]
  refine ⟨result, nextHeap, saved, afterCaller, memoRun, unfoldRun, callerEq, post,
    queryEq, unfoldingExtends, resultAvailable, resultClosed, meaning, nextRealized, runAll, ?_⟩
  intro limit bounded
  exact SourcePruningEnumerationSelectedValue.run_mu_bounded limit 0
    (.mu entry body depth ordinary) beforeCaller.checked.native.machine.heap result nextHeap
    packet.context.ready.semantic available closed bounded (runAll 0)

end MicroCFTA.SourceCurrentPacketMuRun
