import MicroCFTA.SourceEqualityOnePassGraph

/-!
# Complete native scope after a guarded source equality pass

Immediate source returns have no native effect. Live processing derives
its final invariants from actual selected and required receipts and the
native class fold. Erasure supplies only closed available empty roots.
-/
namespace MicroCFTA.SourceEqualityOnePassEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityOnePassGraph

/-- Every successful checked pass retains native validity, semantic heap, cache histories, and closed outputs. -/
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {checked : Except String SourceEqualityPrecheck.Branch} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (trace : Graph unconstrained emptyGuard conjoin clear top checked values before (.ok results) after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  cases trace with
  | unchanged => exact ⟨ready, pure_keeps _ ready.semantic.ready, available, closed⟩
  | emptyChildren => exact ⟨ready, pure_keeps _ ready.semantic.ready, SourceEqualityEmptyPropagation.erased_scope _ _⟩
  | live _ stages => exact stages.effects ready available closed

end MicroCFTA.SourceEqualityOnePassEffects
