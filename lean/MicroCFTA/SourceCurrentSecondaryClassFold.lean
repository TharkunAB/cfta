import MicroCFTA.SourceCurrentSecondaryProjectionScoped
import MicroCFTA.SourceEmptinessClassFold
import MicroCFTA.SourceEmptinessClassFields

/-!
# Anchored projection through the two actual class folds

Each original path has support at one completed gate anchor. The fold
projects its first operand, completes its tail, and runs the actual native
intersection in the returned state. The seeded schedule retains its original
rotation. Projection derives closed native operands without closing the
whole original forest. Later native heaps need no cost-heap premise.
These results use the existing scoped native engine and its actual Step
receipts. They do not transfer execution to GHC or a different worker.
-/
namespace MicroCFTA.SourceCurrentSecondaryClassFold
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEmptinessClassFold
open SourceCurrentSecondaryProjectionScoped (PathSupport operand_effects operand_included)
open InternedGuardedLanguage (meaning)
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- Actual foldr1 retains readiness, physical histories, and its closed resident result. -/
theorem fold_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  induction trace with
  | one operand =>
      have checked := operand_effects unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp))
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | cons operand rest native ih =>
      have first := operand_effects unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp))
      have remaining := ih first.1 (fun value member => first.2.1.available value (available value member))
        (grows_trans growth first.2.1.growth)
        (fun path member => supported path (List.mem_cons_of_mem _ member))
      have last := native.verified remaining.1 (remaining.2.1.available _ first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 (fun _ _ => true) (by intro _ _ _; rfl)
      exact ⟨last.1, first.2.1.trans (remaining.2.1.trans last.2.1), last.2.2.1, last.2.2.2.1⟩

/-- Actual foldr1 retains a common selected subtree of its accepted original forest. -/
theorem fold_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    meaning holds ambient result part := by
  induction trace with
  | one operand =>
      exact operand_included unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp)) (nonroot _ (by simp)) holds ambient symbol terms part accepted (selected _ (by simp))
  | cons operand rest native ih =>
      have first := operand_effects unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp))
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have tailGrowth := grows_trans growth first.2.1.growth
      have remaining := fold_effects unconstrained anchor anchorSemantic anchorReady rest first.1 tailInputs tailGrowth
        (fun path member => supported path (List.mem_cons_of_mem _ member))
      have own := operand_included unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp)) (nonroot _ (by simp)) holds ambient symbol terms part accepted (selected _ (by simp))
      have tail := ih first.1 tailInputs tailGrowth
        (fun path member => supported path (List.mem_cons_of_mem _ member))
        (fun path member => nonroot path (List.mem_cons_of_mem _ member))
        (fun path member => selected path (List.mem_cons_of_mem _ member))
      have checked := native.verified remaining.1 (remaining.2.1.available _ first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨tail, own⟩

/-- The actual seeded schedule retains the same physical invariants, including its empty fallback. -/
theorem seeded_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact ⟨ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons seed rest =>
      exact fold_effects unconstrained anchor anchorSemantic anchorReady trace ready available growth
        (fun path member => supported path ((mem_seededPaths (seed :: rest) path).mp member))

/-- The actual seeded rotation retains each common selected original subtree. -/
theorem seeded_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonempty : paths ≠ []) (nonroot : ∀ path ∈ paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    meaning holds ambient result part := by
  cases paths with
  | nil => exact False.elim (nonempty rfl)
  | cons seed rest =>
      exact fold_included unconstrained anchor anchorSemantic anchorReady trace ready available growth
        (fun path member => supported path ((mem_seededPaths (seed :: rest) path).mp member))
        (fun path member => nonroot path ((mem_seededPaths (seed :: rest) path).mp member))
        holds ambient conjoined symbol terms part accepted
        (fun path member => selected path ((mem_seededPaths (seed :: rest) path).mp member))


open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityNativeScoped SourceEmptinessProjection SourceEmptinessClassFold
open SourceCurrentSecondaryProjectionScoped
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


end MicroCFTA.SourceCurrentSecondaryClassFold
