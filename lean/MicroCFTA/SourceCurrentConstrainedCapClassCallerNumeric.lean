import MicroCFTA.SourceCurrentConstrainedCapClassPassNumeric
import MicroCFTA.SourceCurrentAllocatedClassWorkerActual

/-!
# Complete class passes in the full caller state

Initial numeric reservations construct the actual class pass. Its own reads
retain the filtered probe heap. The caller postcondition uses the same
returned inventory as the query Frame. Both outer result tables and the
fourth memo remain exact while the checked state and Merge memo advance.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapClassCallerNumeric
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedClassPass (Pass PassReads Receipt)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceEqualityProjectionPathDomain (ForestClosed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "foldProfile" => SourceCurrentConstrainedCapClassForecast.foldProfile
local notation "foldFuel" => SourceCurrentConstrainedCapClassForecast.foldFuel
local notation "Reserved" => SourceCurrentConstrainedCapClassForecast.Reserved
local notation "foldDepth" => SourceCurrentConstrainedCapMixedClassPass.foldDepth
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial caller facts and one numeric reservation construct the pass and its complete caller postcondition. -/
theorem complete (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos) (profile : Profile)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (merged : MergeStored before.merge) (caps : ∀ value ∈ values, Cap depth value)
    (reserved : Reserved bits records values.length profile) :
    ∃ results after saved next final,
      ∃ actual : Pass records values before.checked before.merge results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before.checked before.merge results after saved memos final ∧
      Post formulas solver next before (advance before after before.fourth saved) final ∧
      Frame formulas solver next after ∧ Fits (foldProfile records values.length profile) after ∧
      MergeStored saved ∧ (∀ value ∈ results, Cap (foldDepth records depth) value) ∧
      results.length = values.length ∧
      (advance before after before.fourth saved).nodeResults = before.nodeResults ∧
      (advance before after before.fourth saved).edgeResults = before.edgeResults ∧
      (advance before after before.fourth saved).fourth = before.fourth ∧
      SourceCurrentAllocatedClassWorker.pass
        (foldFuel records values.length profile) (foldFuel records values.length profile)
        (foldFuel records values.length profile) (foldFuel records values.length profile)
        (foldFuel records values.length profile) (foldFuel records values.length profile)
        records values before.checked before.merge = .done results after saved ∧
      ∀ e p h m s n,
        foldFuel records values.length profile ≤ e → foldFuel records values.length profile ≤ p →
        foldFuel records values.length profile ≤ h → foldFuel records values.length profile ≤ m →
        foldFuel records values.length profile ≤ s → foldFuel records values.length profile ≤ n →
        SourceCurrentAllocatedClassWorker.pass e p h m s n records values before.checked before.merge =
          .done results after saved := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, returned, numeric,
      savedMerge, outputCaps, length, done⟩ :=
    SourceCurrentConstrainedCapClassPassNumeric.pass depth formulas solver inventory records coherent active values
      before.checked before.merge profile frame fits available domains initial.stored initial.covered merged memos
      initial.globals caps reserved
  have probes := SourceCurrentAllocatedProbeClassPass.pass_heap formulas solver inventory reads coherent active
    initial.ready initial.admitted available domains initial.stored initial.covered initial.globals initial.probes
  have post : Post formulas solver next before (advance before after before.fourth saved) final :=
    ⟨⟨receipt.ready, receipt.admitted,
      initial.sound.advance formulas solver _ before.fourth saved receipt.effects, receipt.stored, receipt.covered,
      SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
      receipt.globals.valid, probes⟩, receipt.effects, receipt.retained, fun _ _ found => found⟩
  refine ⟨results, after, saved, next, final, actual, reads, receipt, post, returned, numeric,
    savedMerge, outputCaps, length, rfl, rfl, rfl, done, ?_⟩
  intro e p h m s n he hp hh hm hs hn
  exact SourceCurrentAllocatedClassWorkerStability.pass_done_stable done he hp hh hm hs hn

end MicroCFTA.SourceCurrentConstrainedCapClassCallerNumeric
