import MicroCFTA.SourceEqualityNativeScoped
import MicroCFTA.SourceEqualityProjectionAPI

/-!
# General projection inside a retained native equality state

getPath changes only the constructor cache. Its wrapper retains the actual
domain cache and both native memo tables. All earlier captured values remain
available through the actual constructor histories.
-/
namespace MicroCFTA.SourceEqualityNativeProjection
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityProjectionGraph
open InternedGuardedLanguage (meaning)

/-- An actual forest projection derives every constructor-cache premise for its native wrapper. -/
theorem forest_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases trace with
  | root union =>
      have checked := union.verified semantic available closed
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | missing => exact ⟨pure_keeps _ semantic.ready, semantic, empty_available _, rfl⟩
  | selected found body =>
      exact SourceEqualityProjectionEffects.node body semantic
        (available _ (select_member found)) (closed _ (select_member found))

/-- A completed general forest projection retains native validity and both idle memo tables. -/
theorem forest_lift [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin before)
    (path : List Int) (values : List (Value Symbol Guard)) (result : Value Symbol Guard)
    (heap : InternedConstructorTemplates.State Symbol Guard) (trace : Forest path values before.machine.heap result heap)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    let after := advanceHeap before heap
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  have checked := forest_effects trace ready.semantic available closed
  exact ⟨ready.advance heap checked.1 checked.2.1, checked.1, checked.2.2.1, checked.2.2.2, rfl, rfl, rfl⟩

/-- Captured original forests admit finite stable projection without resetting domain or memo caches. -/
theorem forest_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (path : List Int) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base values) (closed : ClosedValues values)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before) :
    ∃ result heap, Forest path values before.machine.heap result heap ∧
      let after := advanceHeap before heap
      IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
        after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains ∧
        SourceEqualityRequiredWorkerComplete.StableRun
          (fun fuel readFuel => SourceEqualityProjectionWorker.forest fuel readFuel path values before.machine.heap) result heap := by
  have available : Values before.machine.heap values := fun value member => retained.available value (known value member)
  obtain ⟨result, heap, trace, keeps, semantic, resultAvailable, resultClosed⟩ :=
    SourceEqualityProjectionComplete.forest_complete path values before.machine.heap ready.semantic available closed
  exact ⟨result, heap, trace, ready.advance heap keeps semantic, retained.trans keeps, resultAvailable, resultClosed,
    rfl, rfl, rfl, SourceEqualityProjectionWorkerComplete.forest_stable trace⟩

/-- A proper captured forest path keeps the independent accepted-subterm inclusion in the retained native state. -/
theorem forest_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin before)
    (base : InternedConstructorTemplates.State Symbol Guard) (values : List (Value Symbol Guard))
    (known : Values base values) (retained : Keeps base before.machine.heap) (closed : ClosedValues values)
    (index : Int) (path : List Int) (result : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (trace : Forest (index :: path) values before.machine.heap result heap)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) (index :: path) = some part) : meaning holds ambient result part :=
  SourceEqualityProjectionAPI.forest_included trace ready.semantic
    (fun value member => retained.available value (known value member)) closed holds ambient symbol terms part accepted selected

end MicroCFTA.SourceEqualityNativeProjection
