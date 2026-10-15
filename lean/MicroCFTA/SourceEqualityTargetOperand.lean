import MicroCFTA.SourceEqualityNativeMerge
import MicroCFTA.SourceEqualityNativeProjection

/-!
# A demanded source equality target operand

One operand projects its captured original forest and then performs actual
general merging. Both operations retain the existing full native state.
This graph gives one demand. It does not prescribe other target demands.
-/
namespace MicroCFTA.SourceEqualityTargetOperand
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionGraph
open InternedGuardedLanguage (meaning)

/-- One actual captured-forest projection followed by general merging at its returned heap. -/
inductive Operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (clear : Guard → Bool) (top : Guard) (path : List Int) (values : List (Value Symbol Guard)) :
    SourceRecursiveIntersectionThunks.State width Symbol Guard → Value Symbol Guard →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | force (projection : Forest path values before.machine.heap projected heap)
      (merged : SourceEqualityNativeMerge.Merge clear top projected (advanceHeap before heap) result after) :
      Operand clear top path values before result after

/-- Each actual operand demand retains complete state validity, cache scope, and closed target availability. -/
theorem Operand.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | force projection merged =>
      have projected := SourceEqualityNativeProjection.forest_lift before ready _ values _ _ projection available closed
      have checked := merged.effects projected.1 projected.2.2.1 projected.2.2.2.1
      exact ⟨checked.1, projected.2.1.trans checked.2.1, checked.2.2.1, checked.2.2.2.1,
        checked.2.2.2.2.1.trans projected.2.2.2.2.1,
        checked.2.2.2.2.2.1.trans projected.2.2.2.2.2.1,
        checked.2.2.2.2.2.2.trans projected.2.2.2.2.2.2⟩

/-- Every actual proper-path operand retains each accepted subterm selected from its original forest. -/
theorem Operand.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (nonroot : path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  cases path with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases trace with
      | force projection merged =>
          have projected := SourceEqualityNativeProjection.forest_lift before ready _ values _ _ projection available closed
          exact merged.included projected.1 projected.2.2.1 projected.2.2.2.1 holds ambient clearTrue topTrue part
            (SourceEqualityProjectionAPI.forest_included projection ready.semantic available closed holds ambient symbol terms part accepted selected)

/-- A demanded operand completes from local projection and general merge progress at the existing full native state. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (path : List Int) (values : List (Value Symbol Guard)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ result after, Operand clear top path values before result after ∧ IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  obtain ⟨projected, heap, projection, _⟩ := SourceEqualityProjectionComplete.forest_complete path values before.machine.heap ready.semantic available closed
  have checked := SourceEqualityNativeProjection.forest_lift before ready path values projected heap projection available closed
  obtain ⟨result, after, merged, _⟩ := SourceEqualityNativeMerge.complete emptyGuard conjoin clear top projected (advanceHeap before heap)
    checked.1 checked.2.2.1 checked.2.2.2.1
  have trace : Operand clear top path values before result after := .force projection merged
  exact ⟨result, after, trace, trace.effects ready available closed⟩

/-- Captured original forests retain their actual scope at any later demanded operand. -/
theorem scoped_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (path : List Int) (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
    (known : Values base values) (closed : ClosedValues values) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before) :
    ∃ result after, Operand clear top path values before result after ∧ IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  obtain ⟨result, after, trace, afterReady, keeps, available, closed, _⟩ := complete emptyGuard conjoin clear top path values before ready
    (fun value member => retained.available value (known value member)) closed
  exact ⟨result, after, trace, afterReady, retained.trans keeps, available, closed⟩

end MicroCFTA.SourceEqualityTargetOperand
