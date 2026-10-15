import MicroCFTA.SourceEqualityWarmSelectedRequired
import MicroCFTA.SourceEqualityClosedMemoReads

/-!
# Finite guarded native passes at arbitrary closed warm states

Actual prechecks choose the immediate or live branch. Closed gate progress
derives selection and required paths at the current heap. Actual reached
word ranges then derive the native fold and final empty propagation. The
returned state and both source memo receipts follow from these executions.
-/
namespace MicroCFTA.SourceEqualityWarmOnePass
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceEqualityOnePassGraph SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Actual closed warm scope and reached word checks derive a complete pass without a completed prefix premise. -/
theorem graph (own inherited : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ready : IdleReady top conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (ranges : Ranges source top conjoin SourceMemoGate.plain top (SourceEqualityPrecheck.precheck own inherited) values before) :
    ∃ results after, Execution source top conjoin SourceMemoGate.plain top own inherited values before (.ok results) after := by
  obtain ⟨branch, checked⟩ := SourceEqualityPrecheck.precheck_safe own inherited
  cases branch with
  | unchanged => exact ⟨values, before, .unchanged checked⟩
  | emptyChildren => exact ⟨_, before, .emptyChildren checked⟩
  | classes records =>
      obtain ⟨_, queries, required, heap, _, stages, _, _, _, _, _, _, _, _⟩ :=
        SourceEqualityWarmSelectedRequired.complete values (records.map SourceEqualityClassOrder.Record.paths)
          before.machine.heap ready.semantic available closed
      have plans : SourceEqualityClassFoldGraph.Ranges top conjoin SourceMemoGate.plain top
          (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap before heap) := by
        simp only [SourceEqualityOnePassGraph.Ranges, checked] at ranges
        exact ranges queries before.machine.heap required heap stages
      obtain ⟨results, after, trace, _⟩ := SourceEqualitySelectedClassFold.after_prefix stages ready available closed plans
      exact ⟨results, after, .live checked trace⟩

/-- Every closed warm pass has both actual source memo receipts, full physical effects, and stable finite execution. -/
theorem complete (own inherited : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ready : IdleReady top conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (ranges : Ranges source top conjoin SourceMemoGate.plain top (SourceEqualityPrecheck.precheck own inherited) values before) :
    ∃ results after, ∃ trace : Execution source top conjoin SourceMemoGate.plain top own inherited values before (.ok results) after,
      SourceEqualityClosedMemoReads.PassReads trace ∧ IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Values after.machine.heap results ∧ ClosedValues results ∧
      SourceEqualityOnePassWorkerProofs.StableRun
        (fun g e p h c n => SourceEqualityOnePassWorker.run source top conjoin SourceMemoGate.plain top g e p h c n
          own inherited values before) (.ok results) after ∧
      ∃ arrayBound, ∀ work, arrayBound ≤ work → SourceEqualityOnePassWorkerProofs.StableRun
        (fun g e p h c n => SourceEqualityOnePassWorker.runArray source top conjoin SourceMemoGate.plain top work g e p h c n
          own inherited values before) (.ok results) after := by
  obtain ⟨results, after, trace⟩ := graph own inherited values before ready available closed ranges
  have reads := SourceEqualityClosedMemoReads.pass trace ready.semantic.ready.semantic.1.normal.facts available closed
  have effects := SourceEqualityOnePassEffects.effects trace ready available closed
  exact ⟨results, after, trace, reads, effects.1, effects.2.1, effects.2.2.1, effects.2.2.2,
    SourceEqualityOnePassAPI.stable source top conjoin SourceMemoGate.plain top trace,
    SourceEqualityOnePassAPI.array_stable source top conjoin SourceMemoGate.plain top trace⟩

end MicroCFTA.SourceEqualityWarmOnePass
