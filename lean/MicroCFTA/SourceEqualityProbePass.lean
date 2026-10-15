import MicroCFTA.SourceEqualityProbeSharedEdit
import MicroCFTA.SourceEqualityProbeRequired
import MicroCFTA.SourceEqualityGuardedEdgeGraph

/-!
# Filtered Mu probes through the complete guarded source equality pass

Fresh class captures retain their actual input forest and native state.
Closed gate selection has its proved unchanged constructor heap. Actual
required paths, class right folds, one-pass branches, and literal guarded
reconstruction therefore derive the final probe invariant.
-/
namespace MicroCFTA.SourceEqualityProbePass
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open InternedFreshOrdinaryProbeHeap (Heap)

/-- Each fresh class capture derives preservation through actual shared edits. -/
theorem class_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Class emptyGuard conjoin clear top record values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | edit actual =>
      have initialReady := SourceEqualitySharedTargetState.initial_ready emptyGuard conjoin clear top record values before.machine.heap before
        ready (pure_keeps _ ready.semantic.ready)
      exact SourceEqualityProbeSharedEdit.list emptyGuard conjoin clear top record values before.machine.heap available closed
        actual (SourceEqualitySharedClassEdits.compiled_allowed record) initialReady available closed heap

/-- The actual class right fold retains filtered probes at every tail-returned native state. -/
theorem fold_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top records values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  induction trace with
  | nil => exact heap
  | cons tail head ih =>
      have first := SourceEqualityClassFoldEffects.fold_effects tail ready available closed
      exact class_heap head first.1 first.2.2.1 first.2.2.2 (ih ready available closed heap)

/-- The single final empty propagation makes no change to the returned heap. -/
theorem pass_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Pass emptyGuard conjoin clear top records values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | done actual => exact fold_heap actual ready available closed heap

/-- Closed gate selection and actual required-path reconstruction retain physical filtered probes. -/
theorem selected_required_heap [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values classes queries middle results after}
    {before : NativeState width Symbol Guard}
    (trace : SourceEqualitySelectedRequired.Execution unconstrained values classes before.machine.heap queries middle results after)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} [DecidableEq Symbol]
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap before.machine.heap) : Heap after := by
  have same := SourceClosedGateCache.selection_state trace.selection ready.semantic.ready.semantic.1.normal.facts available closed
  cases same
  obtain ⟨fuel, readFuel, done⟩ := trace.required
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff _ _ _ _ _).mpr ⟨fuel, readFuel, done⟩
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (InternedSourceClassSelection.selected queries)) with
  | node entries =>
      have actual : SourceEqualityRequiredGraph.RequireChildren entries 0 values before.machine.heap results after := by simpa only [compiled] using graph
      exact SourceEqualityProbeRequired.children actual ready.semantic available closed heap

/-- The actual selected/required receipts and selected native fold derive final filtered probes. -/
theorem selected_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {before : NativeState width Symbol Guard}
    {queries : List (InternedSourceClassSelection.Query Symbol Guard)} {middle : State Symbol Guard}
    {required : List (Value Symbol Guard)} {afterRequired : State Symbol Guard} {results : List (Value Symbol Guard)} {after : NativeState width Symbol Guard}
    (trace : SourceEqualitySelectedClassFold.Execution unconstrained emptyGuard conjoin clear top records values before queries middle required afterRequired results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  have first := SourceEqualitySelectedNativeScope.effects trace.stages ready available closed
  have requiredHeap := selected_required_heap trace.stages ready available closed heap
  exact pass_heap trace.narrowed first.2.1 first.2.2.1 first.2.2.2 requiredHeap

/-- Every completed one-pass branch retains filtered probes, including immediate checked errors. -/
theorem one_pass_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {checked : Except String SourceEqualityPrecheck.Branch} {values : List (Value Symbol Guard)} {answer : Except String (List (Value Symbol Guard))}
    {before after : NativeState width Symbol Guard}
    (trace : SourceEqualityOnePassGraph.Graph unconstrained emptyGuard conjoin clear top checked values before answer after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | error | unchanged | emptyChildren => exact heap
  | live _ stages => exact selected_heap stages ready available closed heap

/-- Literal guarded-edge reconstruction derives final filtered probes from its actual resident input and pass. -/
theorem guarded_edge_heap
    [DecidableEq (SourceObservations.Label Formula)]
    [DecidableEq (EdgeKey (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula))]
    {unconstrained : Value (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula) → Bool}
    {emptyGuard : SourceSymbolicIndex.Constraint Formula}
    {conjoin : SourceSymbolicIndex.Constraint Formula → SourceSymbolicIndex.Constraint Formula → SourceSymbolicIndex.Constraint Formula}
    {clear : SourceSymbolicIndex.Constraint Formula → Bool} {top : SourceSymbolicIndex.Constraint Formula}
    {edge result : EdgeValue (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula)}
    {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula)}
    (trace : SourceEqualityGuardedEdgeGraph.Graph unconstrained emptyGuard conjoin clear top edge inherited before result after)
    (ready : IdleReady emptyGuard conjoin before) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (closed : ClosedValues edge.children) (heap : Heap before.machine.heap) : Heap after.machine.heap := by
  cases trace with
  | done _ pass =>
      have available := ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
      have middleHeap := one_pass_heap pass ready available closed heap
      exact InternedFreshOrdinaryProbeHeap.edge edge.entry.key.symbol edge.entry.key.constraint _ _ middleHeap

end MicroCFTA.SourceEqualityProbePass
