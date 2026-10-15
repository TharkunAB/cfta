import MicroCFTA.SourceEmptinessClassFold
import MicroCFTA.SourceEqualityAnnotationProjection
import MicroCFTA.SourceEqualityNativeAnnotationScoped
import MicroCFTA.SourceEqualityNativeDemandFieldHeap

/-!
# Normalized physical fields through actual scoped class folds

Plain projections retain existing edge annotations. Each native leaf uses
the existing scoped engine and its compiled annotation certificates. Fold
induction passes the annotation heap through the actual returned states.
The concrete source constructors discharge the emitted annotation premises.
These states do not include the newer checked constraint-operation heap.
Native container, machine-word, and runtime demand transfers remain separate.
-/
namespace MicroCFTA.SourceEmptinessClassFields
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNativeScoped SourceEmptinessProjection SourceEmptinessClassFold
open SourceEqualityAnnotationHeap (Heap)

/-- Actual plain path projection preserves each physical edge annotation. -/
theorem operand_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | force projection =>
      exact SourceEqualityAnnotationProjection.forest annotation projection ready.semantic available closed heap

/-- Actual foldr1 states preserve annotations through each projection and compiled native leaf. -/
theorem fold_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  induction trace with
  | one operand => exact operand_heap annotation operand ready available closed heap
  | cons operand rest native ih =>
      have first := operand.effects ready available closed
      have firstHeap := operand_heap annotation operand ready available closed heap
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have remaining := rest.effects first.1 tailInputs closed
      have remainingHeap := ih first.1 tailInputs firstHeap
      exact SourceEqualityNativeAnnotationScoped.step annotation emptyValid conjoinedValid native remaining.1
        (remaining.2.1.available _ first.2.2.1) remaining.2.2.1 remainingHeap

/-- The actual seeded fold preserves annotations, including its source empty-list fallback. -/
theorem seeded_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact heap
  | cons seed rest => exact fold_heap annotation emptyValid conjoinedValid trace ready available closed heap

open SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "normalized" => fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities

/-- Concrete source conjunction derives normalized fields through the actual old scoped native step. -/
theorem native_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {left right result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Step top conjoin left right before result after) (ready : IdleReady top conjoin before)
    (leftAvailable : Available before.machine.heap left) (rightAvailable : Available before.machine.heap right)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact SourceEqualityNativeAnnotationScoped.step normalized SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) trace ready leftAvailable rightAvailable heap

/-- Plain projection preserves the same physical field predicate used by the checked engine. -/
theorem operand_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {join : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard join before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap :=
  operand_heap normalized trace ready available closed heap

/-- Actual source foldr1 execution derives the final normalized-field heap without a final-state premise. -/
theorem fold_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold top conjoin values paths before result after) (ready : IdleReady top conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact fold_heap normalized SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) trace ready available closed heap

/-- Actual source seeded execution derives the same final field heap at its own returned state. -/
theorem seeded_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded top conjoin values paths before result after) (ready : IdleReady top conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact seeded_heap normalized SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) trace ready available closed heap

end MicroCFTA.SourceEmptinessClassFields
