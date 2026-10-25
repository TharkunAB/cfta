import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentRequiredQueryMemos
import MicroCFTA.SourceCurrentAllocatedProbeExposure
import MicroCFTA.SourceEqualityRequiredHeadLanguage
import MicroCFTA.SourcePruningEnumerationObservation

namespace MicroCFTA.SourcePruningEnumerationUnion
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat} {EnumGuard : Type}

/-- Actual Union row exposure and reconstruction retain the checked caller and every pending slot. -/
theorem complete [DecidableEq (EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (memos : Memos)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (members : List Node) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : EnumerationState.State Symbol EnumGuard)
    (initial : Context formulas solver inventory beforeCaller memos)
    (available : Available beforeCaller.checked.native.machine.heap (.union entry members depth free))
    (closed : (Value.union entry members depth free).free = [])
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before) :
    ∃ (result : Node) (nextHeap : InternedConstructorTemplates.State Symbol Constraint)
      (saved : Memos) (afterCaller : Caller width)
      (actual : SourceEqualityRequiredHead.Head (.union entry members depth free)
        beforeCaller.checked.native.machine.heap result nextHeap),
      SourceCurrentRequiredQueryMemos.HeadReads actual memos saved ∧
      afterCaller = SourceCurrentAllocatedPartialState.advance beforeCaller
        (advancePhysical beforeCaller.checked ⟨nextHeap, beforeCaller.checked.operations⟩)
        beforeCaller.fourth beforeCaller.merge ∧
      Post formulas solver inventory beforeCaller afterCaller saved ∧
      saved.query = memos.query ∧ Cache.Extends memos.unfolding saved.unfolding ∧
      Available nextHeap result ∧ result.free = [] ∧ SourceEqualityRequiredCache.Ordinary result ∧
      (∀ (holds : Constraint → Language.Term Symbol → Bool)
        (ambient : InternedGuardedLanguage.Env Symbol) (term : Language.Term Symbol),
        InternedGuardedLanguage.meaning holds ambient result term ↔
          InternedGuardedLanguage.meaning holds ambient (.union entry members depth free) term) ∧
      PendingRealized nextHeap before := by
  obtain ⟨result, nextHeap, actual, kept, resultAvailable, resultClosed, ordinary⟩ :=
    SourceEqualityRequiredHead.complete (.union entry members depth free)
      beforeCaller.checked.native.machine.heap initial.ready.semantic.ready available closed
  obtain ⟨saved, reads, globals, retained, querySame⟩ :=
    SourceCurrentRequiredQueryMemos.head_memos actual initial.ready.semantic
      initial.ready.costs available memos initial.globals
  obtain ⟨_headKept, semantic, costs, annotations, _headAvailable⟩ :=
    SourceCurrentRequiredHeapEffects.head
      (SourceCurrentConjunctionEquality.FieldAvailable beforeCaller.checked.operations)
      actual initial.ready.semantic initial.ready.costs initial.ready.good.fields available
  have fields : SourceCurrentConjunctionEquality.Fields beforeCaller.checked.operations nextHeap := by
    exact annotations
  have probes : InternedFreshOrdinaryProbeHeap.Heap nextHeap := by
    exact SourceCurrentAllocatedProbeExposure.head_heap actual initial.ready.semantic
      available initial.probes
  have effects : SourceCurrentConjunctionRowsAllocation.Effects
    (SourceCurrentAllocatedNativeEffects.physical beforeCaller.checked)
    ⟨nextHeap, beforeCaller.checked.operations⟩ := by
    exact ⟨kept, ⟨semantic, costs, initial.ready.good.operations, fields⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  have advancedEffects : SourceCurrentConjunctionRowsAllocation.Effects
    (SourceCurrentAllocatedNativeEffects.physical beforeCaller.checked)
    (SourceCurrentAllocatedNativeEffects.physical
      (advancePhysical beforeCaller.checked ⟨nextHeap, beforeCaller.checked.operations⟩)) := by
    simpa only [SourceCurrentAllocatedQueryMemo.physical_advance] using effects
  refine ⟨result, nextHeap, saved,
    SourceCurrentAllocatedPartialState.advance beforeCaller
      (advancePhysical beforeCaller.checked ⟨nextHeap, beforeCaller.checked.operations⟩)
      beforeCaller.fourth beforeCaller.merge,
    actual, reads, rfl, ?_, querySame, retained, resultAvailable, resultClosed, ordinary, ?_, ?_⟩
  · exact ⟨⟨SourceCurrentConjunctionClassScan.advance_ready beforeCaller.checked
        ⟨nextHeap, beforeCaller.checked.operations⟩ initial.ready effects,
      initial.admitted.advance ⟨nextHeap, beforeCaller.checked.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension beforeCaller.checked
          ⟨nextHeap, beforeCaller.checked.operations⟩ effects),
      initial.sound.advance formulas solver
        (advancePhysical beforeCaller.checked ⟨nextHeap, beforeCaller.checked.operations⟩)
        beforeCaller.fourth beforeCaller.merge advancedEffects,
      initial.stored.grows kept, initial.covered,
      SourceCurrentEmptinessMemo.grows formulas solver kept beforeCaller.fourth initial.correct,
      globals, probes⟩, advancedEffects, Cache.extends_refl _, fun _ _ found => found⟩
  · exact SourceEqualityRequiredHeadLanguage.head_exact actual initial.ready.semantic available closed
  · exact realized_preserved beforeCaller.checked.native.machine.heap nextHeap before before
      realized (EnumerationCompressionFrame.Frame.refl before) kept

end MicroCFTA.SourcePruningEnumerationUnion
