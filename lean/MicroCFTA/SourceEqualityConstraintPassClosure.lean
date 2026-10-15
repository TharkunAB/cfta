import MicroCFTA.SourceEqualityConstraintEditClosure
import MicroCFTA.SourceEqualityAnnotationRequired
import MicroCFTA.SourceEqualityGuardedEdgeGraph

/-!
# Constraint closure through the complete guarded source equality pass

Fresh class captures retain their actual input forest and native state.
Closed gate selection has its proved unchanged constructor heap. Actual
required paths, class right folds, one-pass branches, and literal guarded
reconstruction therefore derive the final constraint heap. Conjunction uses
only constraints from its actual resident operands.
-/
namespace MicroCFTA.SourceEqualityConstraintPassClosure
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceEqualityAnnotationHeap (Heap)

/-- Each fresh class capture derives annotation preservation through actual shared edits. -/
theorem class_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second)) (topValid : annotation top)
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Class emptyGuard conjoin clear top record values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | edit actual =>
      have initialReady := SourceEqualitySharedTargetState.initial_ready emptyGuard conjoin clear top record values before.machine.heap before
        ready (pure_keeps _ ready.semantic.ready)
      exact SourceEqualityConstraintEditClosure.list annotation emptyGuard conjoin clear top record values before.machine.heap available closed
        emptyValid conjoinedValid topValid actual (SourceEqualitySharedClassEdits.compiled_allowed record) initialReady available closed heap

/-- The actual class right fold retains annotations at every tail-returned native state. -/
theorem fold_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second)) (topValid : annotation top)
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top records values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  induction trace with
  | nil => exact heap
  | cons tail head ih =>
      have first := SourceEqualityClassFoldEffects.fold_effects tail ready available closed
      exact class_heap annotation emptyValid conjoinedValid topValid head first.1 first.2.2.1 first.2.2.2 (ih ready available closed heap)

/-- The single final empty propagation makes no change to the returned annotation heap. -/
theorem pass_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second)) (topValid : annotation top)
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Pass emptyGuard conjoin clear top records values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | done actual => exact fold_heap annotation emptyValid conjoinedValid topValid actual ready available closed heap

/-- Closed gate selection and actual required-path reconstruction retain physical annotations. -/
theorem selected_required_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values classes queries middle results after}
    {before : NativeState width Symbol Guard}
    (trace : SourceEqualitySelectedRequired.Execution unconstrained values classes before.machine.heap queries middle results after)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} [DecidableEq Symbol]
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after := by
  have same := SourceClosedGateCache.selection_state trace.selection ready.semantic.ready.semantic.1.normal.facts available closed
  cases same
  obtain ⟨fuel, readFuel, done⟩ := trace.required
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff _ _ _ _ _).mpr ⟨fuel, readFuel, done⟩
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (InternedSourceClassSelection.selected queries)) with
  | node entries =>
      have actual : SourceEqualityRequiredGraph.RequireChildren entries 0 values before.machine.heap results after := by simpa only [compiled] using graph
      exact SourceEqualityAnnotationRequired.children annotation actual ready.semantic available closed heap

/-- The actual selected/required receipts and selected native fold derive final annotations. -/
theorem selected_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second)) (topValid : annotation top)
    {records : List SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {before : NativeState width Symbol Guard}
    {queries : List (InternedSourceClassSelection.Query Symbol Guard)} {middle : State Symbol Guard}
    {required : List (Value Symbol Guard)} {afterRequired : State Symbol Guard} {results : List (Value Symbol Guard)} {after : NativeState width Symbol Guard}
    (trace : SourceEqualitySelectedClassFold.Execution unconstrained emptyGuard conjoin clear top records values before queries middle required afterRequired results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  have first := SourceEqualitySelectedNativeScope.effects trace.stages ready available closed
  have requiredHeap := selected_required_heap annotation trace.stages ready available closed heap
  exact pass_heap annotation emptyValid conjoinedValid topValid trace.narrowed first.2.1 first.2.2.1 first.2.2.2 requiredHeap

/-- Every completed one-pass branch retains annotations, including immediate checked errors. -/
theorem one_pass_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second)) (topValid : annotation top)
    {checked : Except String SourceEqualityPrecheck.Branch} {values : List (Value Symbol Guard)} {answer : Except String (List (Value Symbol Guard))}
    {before after : NativeState width Symbol Guard}
    (trace : SourceEqualityOnePassGraph.Graph unconstrained emptyGuard conjoin clear top checked values before answer after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | error | unchanged | emptyChildren => exact heap
  | live _ stages => exact selected_heap annotation emptyValid conjoinedValid topValid stages ready available closed heap

/-- Literal guarded-edge reconstruction derives final annotations from its actual resident input and pass. -/
theorem guarded_edge_heap (annotation : SourceSymbolicIndex.Constraint Formula → Prop)
    [DecidableEq (SourceObservations.Label Formula)]
    [DecidableEq (EdgeKey (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula))]
    {unconstrained : Value (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula) → Bool}
    {emptyGuard : SourceSymbolicIndex.Constraint Formula}
    {conjoin : SourceSymbolicIndex.Constraint Formula → SourceSymbolicIndex.Constraint Formula → SourceSymbolicIndex.Constraint Formula}
    {clear : SourceSymbolicIndex.Constraint Formula → Bool} {top : SourceSymbolicIndex.Constraint Formula}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second)) (topValid : annotation top)
    {edge result : EdgeValue (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula)}
    {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula)}
    (trace : SourceEqualityGuardedEdgeGraph.Graph unconstrained emptyGuard conjoin clear top edge inherited before result after)
    (ready : IdleReady emptyGuard conjoin before) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (closed : ClosedValues edge.children) (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | done _ pass =>
      have available := ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
      have middleHeap := one_pass_heap annotation emptyValid conjoinedValid topValid pass ready available closed heap
      exact SourceEqualityAnnotationHeap.run annotation _
        (SourceEqualityAnnotationHeap.makeEdge annotation edge.entry.key.symbol edge.entry.key.constraint _ (heap edge.entry.key edge resident)) _ middleHeap

end MicroCFTA.SourceEqualityConstraintPassClosure
