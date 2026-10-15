import MicroCFTA.SourceSecondaryGateProjectionLanguage
import MicroCFTA.SourceSecondaryGateProjectionHeap
import MicroCFTA.SourceEmptinessProjection

/-!
# Anchored projection in the retained scoped native state

Signed paths retain their exact natural-path witnesses. Each actual operand
changes only the constructor heap. It retains both native memo tables and
the domain cache. The anchor supplies gate readiness. Later caller heaps
need semantic readiness and retained anchor records.

These receipts use the existing scoped engine state. They do not transfer
execution to the checked constraint-operation state or to GHC demand.
-/
namespace MicroCFTA.SourceSecondaryGateScopedProjection
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEmptinessProjection
open SourceSecondaryGateProjectionComplete (ForestSupport)
open SourceEqualityAnnotationHeap (Heap)
open InternedGuardedLanguage (meaning)

/-- A signed path has one natural witness with anchored support for the original forest. -/
def PathSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (path : List Int) (values : List (Value Symbol Guard)) : Prop :=
  ∃ natural : EqualityNormalize.Path,
    path = natural.map Int.ofNat ∧ ForestSupport unconstrained anchor natural values

/-- Natural forest support supplies the exact signed path used by the scoped operand. -/
theorem mapped_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)}
    (supported : ForestSupport unconstrained anchor path values) :
    PathSupport unconstrained anchor (path.map Int.ofNat) values := ⟨path, rfl, supported⟩

/-- An anchored false proper forest gate supplies the signed operand support. -/
theorem path_support_of_false [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)}
    (gate : InternedFreshOrdinaryStatefulGateTrace.PathTrace unconstrained values path anchor false anchor)
    (nonroot : path ≠ []) (available : Values anchor values) :
    PathSupport unconstrained anchor (path.map Int.ofNat) values :=
  mapped_support (SourceSecondaryGateProjectionComplete.false_path_support gate nonroot available)

/-- Actual supported operands retain native readiness, physical histories, and closed results. -/
theorem operand_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : PathSupport unconstrained anchor path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  rcases supported with ⟨natural, rfl, supported⟩
  cases trace with
  | force projection =>
      have checked := SourceSecondaryGateProjectionComplete.forest_verified unconstrained anchor
        anchorSemantic anchorReady projection ready.semantic available growth supported
      exact ⟨ready.advance _ checked.1 checked.2.1, checked.1, checked.2.2.1, checked.2.2.2, rfl, rfl, rfl⟩

/-- Proper supported operands retain the selected subtree of each accepted original forest. -/
theorem operand_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : PathSupport unconstrained anchor path values) (nonroot : path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    meaning holds ambient result part := by
  rcases supported with ⟨natural, rfl, supported⟩
  cases natural with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases trace with
      | force projection =>
          exact SourceSecondaryGateProjectionLanguage.forest_included unconstrained anchor anchorSemantic anchorReady
            projection ready.semantic available growth supported holds ambient symbol terms part accepted selected

/-- Actual supported operands retain annotations in their exact returned constructor heap. -/
theorem operand_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : PathSupport unconstrained anchor path values) (fields : Heap annotation before.machine.heap) :
    Heap annotation after.machine.heap := by
  rcases supported with ⟨natural, rfl, supported⟩
  cases trace with
  | force projection =>
      exact SourceSecondaryGateProjectionHeap.forest_heap annotation unconstrained anchor anchorSemantic anchorReady
        projection ready.semantic available growth supported fields

/-- Supported operands derive finite projection in the same retained native state without word checks. -/
theorem operand_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (path : List Int)
    (values : List (Value Symbol Guard)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap) (supported : PathSupport unconstrained anchor path values) :
    ∃ result after, Operand path values before result after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  obtain ⟨natural, same, naturalSupport⟩ := supported
  obtain ⟨result, heap, projected, _⟩ := SourceSecondaryGateProjectionComplete.forest_complete unconstrained anchor
    anchorSemantic anchorReady natural values before.machine.heap ready.semantic available growth naturalSupport
  have actual : Operand path values before result (advanceHeap before heap) := .force (by simpa only [same] using projected)
  exact ⟨result, advanceHeap before heap, actual,
    operand_effects unconstrained anchor anchorSemantic anchorReady actual ready available growth
      ⟨natural, same, naturalSupport⟩⟩

end MicroCFTA.SourceSecondaryGateScopedProjection
