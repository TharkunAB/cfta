import MicroCFTA.SourceClosedGateMemoSelection
import MicroCFTA.SourceEqualityPartialCheckedSource

/-!
# Actual gate memo receipts at closed warm equality prefixes

Both concrete memo tables start empty at each local selection. Closed
inputs leave the unfolding memo unchanged and retain every predicate memo
call. The returned tables are coherent at the exact selected heap. These
receipts do not require the older open-unfolding cost-heap certificate.
-/
namespace MicroCFTA.SourceEqualityClosedMemoReads
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Actual selected stages retain both source memos, their coherence, and the unchanged selection heap. -/
def StageReads {records values before queries middle required heap results after}
    (stages : SourceEqualitySelectedClassFold.Execution source top conjoin SourceMemoGate.plain top records values
      (before : NativeState width Symbol Guard) queries middle required heap results after) : Prop :=
  ∃ predicate,
    SourceMemoClassSelection.Reads values stages.stages.selection InternedFreshOrdinaryUnfoldMemo.empty
      SourceUnconstrainedMemo.empty InternedFreshOrdinaryUnfoldMemo.empty predicate ∧
    InternedFreshOrdinaryUnfoldMemo.Correct middle InternedFreshOrdinaryUnfoldMemo.empty ∧
    SourceUnconstrainedMemo.Correct middle predicate ∧ middle = before.machine.heap

/-- A concrete one-pass graph records precisely the source memo calls selected by its actual branch. -/
inductive PassReads {checked : Except String SourceEqualityPrecheck.Branch} {values : List (Value Symbol Guard)}
    {before : NativeState width Symbol Guard} :
    {answer : Except String (List (Value Symbol Guard))} → {after : NativeState width Symbol Guard} →
      SourceEqualityOnePassGraph.Graph source top conjoin SourceMemoGate.plain top checked values before answer after → Prop where
  | error (actual : checked = .error message) : PassReads (.error actual)
  | unchanged (actual : checked = .ok .unchanged) : PassReads (.unchanged actual)
  | emptyChildren (actual : checked = .ok .emptyChildren) : PassReads (.emptyChildren actual)
  | live (actual : checked = .ok (.classes records))
      (stages : SourceEqualitySelectedClassFold.Execution source top conjoin SourceMemoGate.plain top records values before queries middle required heap results after)
      (reads : StageReads stages) : PassReads (.live actual stages)

/-- Every actual closed warm pass derives both memo tables from physical input facts. -/
theorem pass {checked values before answer after}
    (trace : SourceEqualityOnePassGraph.Graph source top conjoin SourceMemoGate.plain top checked values
      (before : NativeState width Symbol Guard) answer after)
    (facts : Facts before.machine.heap) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    PassReads trace := by
  cases trace with
  | error actual => exact .error actual
  | unchanged actual => exact .unchanged actual
  | emptyChildren actual => exact .emptyChildren actual
  | live actual stages =>
      obtain ⟨predicate, reads, correct⟩ := SourceClosedGateMemoSelection.selection stages.stages.selection facts available closed
        InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty (SourceUnconstrainedMemo.empty_correct _)
      exact .live actual stages ⟨predicate, reads, InternedFreshOrdinaryUnfoldMemo.empty_correct _, correct,
        SourceClosedGateCache.selection_state stages.stages.selection facts available closed⟩

/-- A guarded edge retains the exact physical payload and its concrete closed source memo receipts. -/
inductive EdgeReads {edge inherited before} :
    {result : EdgeValue Symbol Guard} → {after : NativeState width Symbol Guard} →
      SourceEqualityPCSNativeEdge.Execution edge inherited (before : NativeState width Symbol Guard) result after → Prop where
  | done {payload results middle} (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok payload)
      (pass : SourceEqualityOnePassGraph.Execution source top conjoin SourceMemoGate.plain top payload inherited edge.children before (.ok results) middle)
      (reads : PassReads pass) : EdgeReads (.done physical pass)

/-- Every actual closed warm edge prefix supplies both memo receipts without a future heap or cost-heap premise. -/
theorem edge {edge result inherited before after}
    (trace : SourceEqualityPCSNativeEdge.Execution edge inherited (before : NativeState width Symbol Guard) result after)
    (facts : Facts before.machine.heap) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (closed : ClosedValues edge.children) : EdgeReads trace := by
  cases trace with
  | done physical actual => exact .done physical actual (pass actual facts (facts.cached.edges _ _ resident) closed)

end MicroCFTA.SourceEqualityClosedMemoReads
