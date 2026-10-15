import MicroCFTA.SourceEmptinessProjection
import MicroCFTA.SourceEqualityAnnotationProjection

/-!
# Plain path projection with local closedness

A proper forest path selects one original top child. Only that selected
child must be closed. Unrelated original siblings may remain open. The root
path unions all original values, so it still requires all of them closed.
The closedness predicate has no heap parameter and remains the same as the
heap grows. The selected top child must be closed as a whole. This result
does not admit open branches deeper inside that child or derive closedness
from the secondary gate. Native states use the existing scoped engine.
-/
namespace MicroCFTA.SourceEmptinessProjectionLocal
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open InternedGuardedLanguage (meaning)

/-- Root union needs every value closed; a proper path needs only its selected top child closed. -/
def PathClosed (values : List (Value Symbol Guard)) : List Int → Prop
  | [] => ClosedValues values
  | index :: _ => ∀ value, select values index = some value → value.free = []

/-- A fully closed original forest supplies local closedness for every path. -/
theorem PathClosed.of_closed {values : List (Value Symbol Guard)} (closed : ClosedValues values)
    (path : List Int) : PathClosed values path := by
  cases path with
  | nil => exact closed
  | cons index rest => exact fun value found => closed value (select_member found)

/-- Actual forest projection retains its heap and closed result using only path-local input closedness. -/
theorem forest_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : PathClosed values path) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases trace with
  | root union =>
      have checked := union.verified semantic available closed
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | missing => exact ⟨pure_keeps _ semantic.ready, semantic, empty_available _, rfl⟩
  | selected found body =>
      exact SourceEqualityProjectionEffects.node body semantic (available _ (select_member found)) (closed _ found)

/-- A proper path retains its selected accepted subtree while unrelated forest siblings may be open. -/
theorem forest_included [DecidableEq (EdgeKey Symbol Guard)]
    {index : Int} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (trace : Forest (index :: path) values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : PathClosed values (index :: path))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) (index :: path) = some part) :
    meaning holds ambient result part := by
  rw [SourceEqualityNeededMeaning.lookup_cons] at selected
  obtain ⟨term, termAt, partAt⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨value, valueAt, valueAccepted⟩ := SourceEqualityProjectionLanguage.all₂_signed accepted index term termAt
  cases trace with
  | missing absent => rw [absent] at valueAt; cases valueAt
  | selected found body =>
      have same := Option.some.inj (found.symm.trans valueAt)
      subst value
      exact SourceEqualityProjectionLanguage.node body semantic (available _ (select_member found))
        (closed _ found) holds ambient term part valueAccepted partAt

/-- Every locally closed forest path has finite actual projection with its returned heap. -/
theorem forest_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (values : List (Value Symbol Guard)) (before : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (closed : PathClosed values path) :
    ∃ result after, Forest path values before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases path with
  | nil => exact SourceEqualityProjectionComplete.forest_complete [] values before semantic available closed
  | cons index path =>
      cases found : select values index with
      | none => exact ⟨.empty, before, .missing found, pure_keeps _ semantic.ready, semantic, empty_available _, rfl⟩
      | some value =>
          obtain ⟨result, after, body, effects⟩ := SourceEqualityProjectionComplete.complete path value before semantic
            (available _ (select_member found)) (closed _ found)
          exact ⟨result, after, .selected found body, effects⟩

/-- Actual plain projection preserves annotations using only the selected top child's closedness. -/
theorem operand_local_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEmptinessProjection.Operand path values before result after)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : PathClosed values path)
    (heap : SourceEqualityAnnotationHeap.Heap annotation before.machine.heap) :
    SourceEqualityAnnotationHeap.Heap annotation after.machine.heap := by
  cases trace with
  | force projection =>
      cases projection with
      | root union => exact SourceEqualityAnnotationProjection.union annotation union ready.semantic available closed heap
      | missing => exact heap
      | selected found body =>
          exact SourceEqualityAnnotationProjection.node annotation body ready.semantic
            (available _ (select_member found)) (closed _ found) heap

end MicroCFTA.SourceEmptinessProjectionLocal

namespace MicroCFTA.SourceEmptinessProjection
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEmptinessProjectionLocal
open InternedGuardedLanguage (meaning)

/-- A locally closed operand retains its actual constructor, domain, and memo states. -/
theorem Operand.local_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : PathClosed values path) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | force projection =>
      have checked := SourceEmptinessProjectionLocal.forest_effects projection ready.semantic available closed
      exact ⟨ready.advance _ checked.1 checked.2.1, checked.1, checked.2.2.1, checked.2.2.2, rfl, rfl, rfl⟩

/-- A locally closed proper operand keeps the selected subtree of the accepted original forest. -/
theorem Operand.local_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : PathClosed values path) (nonroot : path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  cases path with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases trace with
      | force projection =>
          exact SourceEmptinessProjectionLocal.forest_included projection ready.semantic available closed
            holds ambient symbol terms part accepted selected

/-- Local closedness derives finite operand projection without closing unrelated original siblings. -/
theorem local_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (path : List Int)
    (values : List (Value Symbol Guard)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (closed : PathClosed values path) :
    ∃ result after, Operand path values before result after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  obtain ⟨result, heap, trace, _⟩ := SourceEmptinessProjectionLocal.forest_complete path values before.machine.heap
    ready.semantic available closed
  let actual : Operand path values before result (advanceHeap before heap) := .force trace
  exact ⟨result, advanceHeap before heap, actual, actual.local_effects ready available closed⟩

end MicroCFTA.SourceEmptinessProjection
