import MicroCFTA.SourceEqualitySelectedRecords
import MicroCFTA.SourceEqualityClassFoldAPI

/-!
# Actual native scope after source selection and required paths

Closed gate selection retains its original constructor heap. Required-path
reconstruction returns its literal heap with both histories. Advancing that
heap preserves the actual domain cache and both warm native memo tables.
-/
namespace MicroCFTA.SourceEqualitySelectedNativeScope
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph

/-- Actual selected and required stages derive every full-native entry invariant for class narrowing. -/
theorem effects [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values classes queries middle results heap}
    {before : NativeState width Symbol Guard}
    (trace : SourceEqualitySelectedRequired.Execution unconstrained values classes before.machine.heap queries middle results heap)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} [DecidableEq Symbol]
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    Keeps before.machine.heap heap ∧ IdleReady emptyGuard conjoin (advanceHeap before heap) ∧ Values heap results ∧ ClosedValues results := by
  have semantic := (SourceEqualitySelectedRequired.exact trace ready.semantic available closed).1
  have same := SourceClosedGateCache.selection_state trace.selection ready.semantic.ready.semantic.1.normal.facts available closed
  cases same
  obtain ⟨fuel, readFuel, done⟩ := trace.required
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff _ _ _ _ _).mpr ⟨fuel, readFuel, done⟩
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (InternedSourceClassSelection.selected queries)) with
  | node entries =>
      have actual : SourceEqualityRequiredGraph.RequireChildren entries 0 values before.machine.heap results heap := by simpa only [compiled] using graph
      have checked := SourceEqualityRequiredListFacts.children_verified actual ready.semantic.ready available closed
      exact ⟨checked.1, ready.advance heap checked.1 semantic, checked.2⟩

end MicroCFTA.SourceEqualitySelectedNativeScope
