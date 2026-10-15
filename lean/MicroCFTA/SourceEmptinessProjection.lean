import MicroCFTA.SourceEqualityNativeProjection

/-!
# Plain path operands for the conservative emptiness check

The new emptiness paths do not call mergeAlternatives. Each operand retains
its actual getPath result and returned constructor heap. The surrounding
native memo tables and domain state remain unchanged. Native requests use
the existing scoped engine and retain its separate source boundaries.
-/
namespace MicroCFTA.SourceEmptinessProjection
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open InternedGuardedLanguage (meaning)

/-- A plain operand retains the actual projection cache without a merge call. -/
inductive Operand [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (path : List Int) (values : List (Value Symbol Guard)) :
    SourceRecursiveIntersectionThunks.State width Symbol Guard → Value Symbol Guard →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | force (projection : SourceEqualityProjectionGraph.Forest path values before.machine.heap result heap) :
      Operand path values before result (advanceHeap before heap)

/-- Plain projection derives closed resident output and retains every surrounding native table. -/
theorem Operand.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | force projection => exact SourceEqualityNativeProjection.forest_lift before ready _ _ _ _ projection available closed

/-- A proper operand path retains the selected subtree of an accepted original forest. -/
theorem Operand.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (nonroot : path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  cases path with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases trace with
      | force projection =>
          exact SourceEqualityProjectionAPI.forest_included projection ready.semantic available closed
            holds ambient symbol terms part accepted selected

/-- Each captured closed operand has a finite projection in the same surrounding native state. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (path : List Int)
    (values : List (Value Symbol Guard)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ result after, Operand path values before result after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  obtain ⟨result, heap, trace, _⟩ := SourceEqualityProjectionComplete.forest_complete path values before.machine.heap
    ready.semantic available closed
  let actual : Operand path values before result (advanceHeap before heap) := .force trace
  exact ⟨result, advanceHeap before heap, actual, actual.effects ready available closed⟩

end MicroCFTA.SourceEmptinessProjection
