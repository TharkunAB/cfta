import MicroCFTA.SourceEmptinessTasks
import MicroCFTA.SourceEmptinessClassFields
import MicroCFTA.SourceEmptinessTaskRows

/-!
# Normalized physical fields through captured task forces

A first force uses the original forest stored in its captured cell.
Cell readiness supplies the closed available inputs to the actual fold.
Direct values and completed task hits leave the native state unchanged.
Exposure retains its actual row-read heap. Pure capture preserves that heap.
These results concern the existing scoped native state. They do not transfer
execution to the newer checked constraint-operation state or to a GHC heap.
-/
namespace MicroCFTA.SourceEmptinessTaskFields
open InternedConstructorTemplates
open SourceEmptinessTasks
open SourceEqualityAnnotationHeap (Heap)

/-- Actual task forces preserve annotations at their returned native heap. -/
theorem force_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {task : Task Symbol Guard} {before after : State width Symbol Guard} {value : Value Symbol Guard}
    (trace : Force emptyGuard conjoin task before value after) (ready : Ready emptyGuard conjoin before)
    (heap : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases trace with
  | value => exact heap
  | hit => exact heap
  | miss found _ fold =>
      have original := ready.cells _ _ found
      exact SourceEmptinessClassFields.fold_heap annotation emptyValid conjoinedValid fold ready.native
        original.1 original.2.1 heap

open SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Concrete source task forcing derives the final normalized-field heap. -/
theorem force_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {task : Task Symbol Guard} {before after : State width Symbol Guard} {value : Value Symbol Guard}
    (trace : Force top conjoin task before value after) (ready : Ready top conjoin before)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.native.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.native.machine.heap := by
  cases trace with
  | value => exact heap
  | hit => exact heap
  | miss found _ fold =>
      have original := ready.cells _ _ found
      exact SourceEmptinessClassFields.fold_fields fold ready.native original.1 original.2.1 heap

/-- Actual row exposure preserves normalized fields through its read and delayed capture. -/
theorem expose_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {join : Guard → Guard → Guard}
    {value : Value Symbol Guard} {before after : State width Symbol Guard}
    {rows : List (List (Task Symbol Guard))}
    (trace : SourceEmptinessTaskRows.Expose value before rows after) (ready : Ready emptyGuard join before)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.native.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.native.machine.heap := by
  cases trace with
  | read available closed actual =>
      have fields := SourceEmptinessExposure.read_fields actual ready.native.semantic heap available closed
      simpa only [SourceEmptinessTaskRows.captureRows_native, advanceNative,
        SourceEqualityNativeScoped.advanceHeap, SourceRecursiveIntersectionThunks.advance] using fields

end MicroCFTA.SourceEmptinessTaskFields
