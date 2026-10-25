import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceQueryUnfoldMemo
import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap
import MicroCFTA.SourcePruningEnumerationObservation

namespace MicroCFTA.SourcePruningEnumerationMu
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

/-- One memoized outer Mu unfolding retains the actual checked caller and every pending slot. -/
theorem complete [DecidableEq (EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (memos : Memos)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Node)
    (before : EnumerationState.State Symbol EnumGuard)
    (initial : Context formulas solver inventory beforeCaller memos)
    (available : Available beforeCaller.checked.native.machine.heap (.mu entry body depth ordinary))
    (closed : (Value.mu entry body depth ordinary).free = [])
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before) :
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
      PendingRealized nextHeap before := by
  obtain ⟨result, nextHeap, unfolded, kept, semantic, resultAvailable, language⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary)
      beforeCaller.checked.native.machine.heap initial.ready.semantic available
  obtain ⟨saved, executed, querySame, globals, retained⟩ :=
    SourceQueryUnfoldMemo.run_memos_of_unfold (.mu entry body depth ordinary) result
      beforeCaller.checked.native.machine.heap nextHeap unfolded initial.ready.semantic
      initial.ready.costs available memos initial.globals
  have costs : InternedFreshOrdinaryCostHeap.Heap nextHeap := by
    simpa only [unfolded, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap (.mu entry body depth ordinary)
        beforeCaller.checked.native.machine.heap initial.ready.semantic.ready.semantic.1
        initial.ready.semantic.ready.semantic.2 initial.ready.costs available
  have fields : SourceCurrentConjunctionEquality.Fields beforeCaller.checked.operations nextHeap := by
    simpa only [unfolded, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryStoredConstraintHeap.unfold_heap
        (SourceCurrentConjunctionEquality.FieldAvailable beforeCaller.checked.operations)
        (.mu entry body depth ordinary) beforeCaller.checked.native.machine.heap
        initial.ready.semantic.ready.semantic.1.normal.facts initial.ready.good.fields available
  have probes : InternedFreshOrdinaryProbeHeap.Heap nextHeap := by
    simpa only [unfolded, InternedNestedConstruction.Outcome.state] using
      SourceEqualityProbeUnfold.unfold (.mu entry body depth ordinary)
        beforeCaller.checked.native.machine.heap initial.ready.semantic.ready.semantic.1
        initial.probes available
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
    executed, unfolded, rfl, ?_, querySame, retained, resultAvailable, ?_, language, ?_⟩
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
  · exact InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
      beforeCaller.checked.native.machine.heap initial.ready.semantic.ready.semantic.1
      available closed result nextHeap unfolded
  · exact realized_preserved beforeCaller.checked.native.machine.heap nextHeap before before
      realized (EnumerationCompressionFrame.Frame.refl before) kept

end MicroCFTA.SourcePruningEnumerationMu
