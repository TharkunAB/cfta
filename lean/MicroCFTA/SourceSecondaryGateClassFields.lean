import MicroCFTA.SourceSecondaryGateClassFold
import MicroCFTA.SourceEmptinessClassFields

/-!
# Physical annotations through class folds supported by secondary gates

Each actual projection uses support at one completed gate anchor.
The fold passes annotations through its exact returned native states.
Concrete top and conjunction constructors derive normalized query fields.
Later caller heaps do not need the anchor's cost invariant.
-/
namespace MicroCFTA.SourceSecondaryGateClassFields
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityNativeScoped SourceEmptinessProjection SourceEmptinessClassFold
open SourceSecondaryGateScopedProjection SourceSecondaryGateClassFold
open SourceEqualityAnnotationHeap (Heap)

/-- Actual foldr1 projection and native requests preserve each physical annotation predicate. -/
theorem fold_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  induction trace with
  | one operand =>
      exact operand_heap annotation unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp)) heap
  | cons operand rest native ih =>
      have first := operand_effects unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp))
      have firstHeap := operand_heap annotation unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp)) heap
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have tailGrowth := grows_trans growth first.2.1.growth
      have tailSupport := fun path member => supported path (List.mem_cons_of_mem _ member)
      have remaining := fold_effects unconstrained anchor anchorSemantic anchorReady rest first.1 tailInputs tailGrowth tailSupport
      have remainingHeap := ih first.1 tailInputs tailGrowth tailSupport firstHeap
      exact SourceEqualityNativeAnnotationScoped.step annotation emptyValid conjoinedValid native remaining.1
        (remaining.2.1.available _ first.2.2.1) remaining.2.2.1 remainingHeap

/-- The actual seeded rotation retains annotations without a whole-original-forest closedness premise. -/
theorem seeded_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact heap
  | cons seed rest =>
      exact fold_heap annotation unconstrained anchor anchorSemantic anchorReady emptyValid conjoinedValid trace ready
        available growth (fun path member => supported path ((mem_seededPaths (seed :: rest) path).mp member)) heap

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "normalized" => fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities

/-- Concrete source constructors derive normalized fields through the actual supported foldr1. -/
theorem fold_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold top conjoin values paths before result after) (ready : IdleReady top conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact fold_heap normalized unconstrained anchor anchorSemantic anchorReady SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) trace ready available growth supported heap

/-- Concrete source constructors derive normalized fields through the actual supported seeded query. -/
theorem seeded_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded top conjoin values paths before result after) (ready : IdleReady top conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact seeded_heap normalized unconstrained anchor anchorSemantic anchorReady SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) trace ready available growth supported heap

end MicroCFTA.SourceSecondaryGateClassFields
