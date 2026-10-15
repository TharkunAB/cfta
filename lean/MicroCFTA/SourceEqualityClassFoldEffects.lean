import MicroCFTA.SourceEqualityClassFoldGraph

/-!
# Scoped native effects of the source class right fold

Each class captures its actual entry heap. Local target receipts derive
its output scope. The right fold composes these real histories. Final
empty propagation preserves scope without changing the native state.
-/
namespace MicroCFTA.SourceEqualityClassFoldEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open SourceEqualitySharedTargetState SourceEqualitySharedEditGraph SourceEqualitySharedEditEffects
open SourceEqualityClassFoldGraph

private theorem shared_list [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
    (known : Values base originals) (closed : ClosedValues originals) {edits values before results after}
    (trace : EditList (width := width) emptyGuard conjoin clear top record originals edits values before results after)
    (allowed : Allowed record edits) (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (inputClosed : ClosedValues values) :
    SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Values after.native.machine.heap results ∧ ClosedValues results := by
  cases trace with
  | leaf => exact ⟨ready, pure_keeps _ ready.native.semantic.ready, available, inputClosed⟩
  | children trace => exact SourceEqualitySharedEditEffects.children emptyGuard conjoin clear top record originals base known closed trace allowed ready available inputClosed

/-- A fresh actual class edit retains native validity, semantic heap, cache histories, and closed outputs. -/
theorem class_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Class emptyGuard conjoin clear top record values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  cases trace with
  | edit actual =>
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before ready (pure_keeps _ ready.semantic.ready)
      have checked := shared_list emptyGuard conjoin clear top record values before.machine.heap available closed actual
        (SourceEqualitySharedClassEdits.compiled_allowed record) initialReady available closed
      exact ⟨checked.1.native, checked.2⟩

/-- Every completed source right fold composes the exact native states and constructor histories. -/
theorem fold_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top records values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  induction trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, available, closed⟩
  | cons tail head ih =>
      have first := ih ready available closed
      have last := class_effects head first.1 first.2.2.1 first.2.2.2
      exact ⟨last.1, first.2.1.trans last.2.1, last.2.2⟩

/-- Final literal empty propagation retains the complete native state returned by the fold. -/
theorem pass_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Pass emptyGuard conjoin clear top records values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  cases trace with
  | done fold =>
      have checked := fold_effects fold ready available closed
      exact ⟨checked.1, checked.2.1, SourceEqualityEmptyPropagation.scope _ _ checked.2.2.1 checked.2.2.2⟩

end MicroCFTA.SourceEqualityClassFoldEffects
