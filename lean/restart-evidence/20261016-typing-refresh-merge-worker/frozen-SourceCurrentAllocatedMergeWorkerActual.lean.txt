import MicroCFTA.SourceCurrentAllocatedMergeWorkerSound
import MicroCFTA.SourceCurrentAllocatedMergeWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedMerge
import MicroCFTA.SourceCurrentAllocatedProbeMerge
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Checked receipts for literal allocated merge execution

A completed worker derives the same allocated call before semantic
verification. Its result, operation state, heap, and merge table stay exact.
Global query reads remain an explicit constructed schedule. The worker does
not execute a concrete host query table or prove GHC forcing behavior.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeWorkerActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The supplied literal return derives its own full checked receipt and probe heap. -/
theorem verified (inventory : Inventory) {fuel selectionFuel : Nat}
    {input output : Value Symbol Guard} {before : Checked width} {after : Physical} {memo saved : Memo}
    (done : SourceCurrentAllocatedMergeWorker.call literalClear fuel selectionFuel input (physical before) memo =
      .done output after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (available : Available before.native.machine.heap input) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (probes : ProbeHeap before.native.machine.heap) :
    ∃ final, SourceCurrentAllocatedMerge.Receipt formulas solver inventory literalClear input before memo output
      (advancePhysical before after) saved memos final ∧ ProbeHeap after.heap := by
  have actual := SourceCurrentAllocatedMergeWorkerSound.call_sound done
  obtain ⟨final, receipt⟩ := SourceCurrentAllocatedMerge.verified formulas solver inventory literalClear
    (SourceCurrentAllocatedMerge.literalClear_true formulas solver) (.done actual) ready admitted stored covered available memos valid
  have finalProbes := SourceCurrentAllocatedProbeMerge.allocated_call_heap actual
    ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩ stored available probes
  exact ⟨final, receipt, finalProbes⟩

/-- A literal merge return retains the full caller context and its warm result families. -/
theorem caller {inventory : Inventory} {fuel selectionFuel : Nat} {before : Caller width} {after : Physical}
    {input output : Value Symbol Guard} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap input)
    (done : SourceCurrentAllocatedMergeWorker.call literalClear fuel selectionFuel input (physical before.checked) before.merge =
      .done output after saved) :
    ∃ final, Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) before.fourth saved) final ∧
      Available after.heap output ∧ (input.free = [] → output.free = []) ∧
      ∀ ambient, SourceCurrentMemoMergeLanguage.Covers (SourceEqualityPCSGuard.holds formulas solver) ambient input output := by
  obtain ⟨final, receipt, probes⟩ := verified formulas solver inventory done initial.ready initial.admitted initial.stored
    initial.covered available memos initial.globals initial.probes
  refine ⟨final, ⟨⟨receipt.ready, receipt.admitted,
    initial.sound.advance formulas solver _ before.fourth saved receipt.effects, receipt.stored, receipt.covered,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
    receipt.globals.valid, probes⟩, receipt.effects, receipt.retained, fun _ _ found => found⟩,
    receipt.available, receipt.closed, receipt.included⟩

/-- Legitimate warm entry facts construct a stable literal merge return and its complete caller receipt. -/
theorem finite {inventory : Inventory} {before : Caller width} {input : Value Symbol Guard} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap input) :
    ∃ output after saved final workBound selectionBound,
      (∀ workFuel selectionFuel, workBound ≤ workFuel → selectionBound ≤ selectionFuel →
        SourceCurrentAllocatedMergeWorker.call literalClear workFuel selectionFuel input (physical before.checked) before.merge =
          .done output after saved) ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) before.fourth saved) final ∧
      Available after.heap output ∧ (input.free = [] → output.free = []) ∧
      ∀ ambient, SourceCurrentMemoMergeLanguage.Covers (SourceEqualityPCSGuard.holds formulas solver) ambient input output := by
  obtain ⟨output, after, saved, actual, _⟩ := SourceCurrentAllocatedMergePhysical.call_complete literalClear input
    (physical before.checked) before.merge
    ⟨initial.ready.semantic, initial.ready.costs, initial.ready.good.operations, initial.ready.good.fields⟩
    initial.stored available
  obtain ⟨workBound, selectionBound, stable⟩ := SourceCurrentAllocatedMergeWorkerCompletion.call_complete actual
  obtain ⟨final, post, resident, closed, included⟩ := caller formulas solver initial available
    (stable workBound selectionBound (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨output, after, saved, final, workBound, selectionBound, stable, post, resident, closed, included⟩

end MicroCFTA.SourceCurrentAllocatedMergeWorkerActual
