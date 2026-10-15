import MicroCFTA.SourceEqualityProjectionPathDomain
import MicroCFTA.SourceEmptinessClassFields

/-!
# Class folds with closed selected ordinary paths

Each projection needs closedness only at its selected ordinary-path leaves.
Unrelated original siblings can remain open at several ordinary levels.
Actual native requests still receive closed resident operands. Recursive
heads retain a closed-input premise. The two source schedules retain their
distinct projection and native histories. Gate-to-domain correspondence,
scoped completion, and machine ranges remain unproved.
-/
namespace MicroCFTA.SourceEmptinessClassFold
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEmptinessProjection
open SourceEqualityProjectionPathDomain (ForestClosed)
open InternedGuardedLanguage (meaning)

/-- Actual foldr1 needs closedness only of each selected ordinary-path leaf. -/
theorem Fold.local_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ∀ path ∈ paths, ForestClosed path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  induction trace with
  | one operand =>
      have checked := operand.path_effects ready available (closed _ (by simp))
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | cons operand rest native ih =>
      have first := operand.path_effects ready available (closed _ (by simp))
      have remaining := ih first.1 (fun value member => first.2.1.available value (available value member))
        (fun path member => closed path (List.mem_cons_of_mem _ member))
      have last := native.verified remaining.1 (remaining.2.1.available _ first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 (fun _ _ => true) (by intro _ _ _; rfl)
      exact ⟨last.1, first.2.1.trans (remaining.2.1.trans last.2.1), last.2.2.1, last.2.2.2.1⟩

/-- Actual foldr1 retains common accepted subtrees with the ordinary-path domain. -/
theorem Fold.local_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ∀ path ∈ paths, ForestClosed path values)
    (nonroot : ∀ path ∈ paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    meaning holds ambient result part := by
  induction trace with
  | one operand =>
      exact operand.path_included ready available (closed _ (by simp)) (nonroot _ (by simp))
        holds ambient symbol terms part accepted (selected _ (by simp))
  | cons operand rest native ih =>
      have first := operand.path_effects ready available (closed _ (by simp))
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have tailClosed := fun path member => closed path (List.mem_cons_of_mem _ member)
      have remaining := rest.local_effects first.1 tailInputs tailClosed
      have own := operand.path_included ready available (closed _ (by simp)) (nonroot _ (by simp))
        holds ambient symbol terms part accepted (selected _ (by simp))
      have tail := ih first.1 tailInputs tailClosed
        (fun path member => nonroot path (List.mem_cons_of_mem _ member))
        (fun path member => selected path (List.mem_cons_of_mem _ member))
      have checked := native.verified remaining.1 (remaining.2.1.available _ first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨tail, own⟩

/-- The seeded schedule also needs closedness only of its selected ordinary-path leaves. -/
theorem Seeded.local_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ∀ path ∈ paths, ForestClosed path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact ⟨ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons seed rest =>
      exact Fold.local_effects trace ready available
        (fun path member => closed path ((mem_seededPaths (seed :: rest) path).mp member))

/-- The seeded schedule preserves every common selected subtree in the ordinary-path domain. -/
theorem Seeded.local_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ∀ path ∈ paths, ForestClosed path values)
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
      exact Fold.local_included trace ready available
        (fun path member => closed path ((mem_seededPaths (seed :: rest) path).mp member))
        (fun path member => nonroot path ((mem_seededPaths (seed :: rest) path).mp member))
        holds ambient conjoined symbol terms part accepted
        (fun path member => selected path ((mem_seededPaths (seed :: rest) path).mp member))

end MicroCFTA.SourceEmptinessClassFold

namespace MicroCFTA.SourceEmptinessClassFields
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeScoped SourceEmptinessProjection SourceEmptinessClassFold
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceEqualityAnnotationHeap (Heap)

/-- Local closedness preserves annotations through each actual projection and native request. -/
theorem fold_local_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ∀ path ∈ paths, ForestClosed path values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  induction trace with
  | one operand => exact SourceEqualityProjectionPathDomain.operand_path_heap annotation operand ready available (closed _ (by simp)) heap
  | cons operand rest native ih =>
      have first := operand.path_effects ready available (closed _ (by simp))
      have firstHeap := SourceEqualityProjectionPathDomain.operand_path_heap annotation operand ready available (closed _ (by simp)) heap
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have tailClosed := fun path member => closed path (List.mem_cons_of_mem _ member)
      have remaining := rest.local_effects first.1 tailInputs tailClosed
      have remainingHeap := ih first.1 tailInputs tailClosed firstHeap
      exact SourceEqualityNativeAnnotationScoped.step annotation emptyValid conjoinedValid native remaining.1
        (remaining.2.1.available _ first.2.2.1) remaining.2.2.1 remainingHeap

/-- The actual seeded schedule retains annotations with closedness only at selected ordinary-path leaves. -/
theorem seeded_local_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ∀ path ∈ paths, ForestClosed path values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact heap
  | cons seed rest =>
      exact fold_local_heap annotation emptyValid conjoinedValid trace ready available
        (fun path member => closed path ((mem_seededPaths (seed :: rest) path).mp member)) heap

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Actual seeded source requests derive normalized query fields in the ordinary-path domain. -/
theorem seeded_local_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded top conjoin values paths before result after) (ready : IdleReady top conjoin before)
    (available : Values before.machine.heap values) (closed : ∀ path ∈ paths, ForestClosed path values)
    (heap : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact seeded_local_heap (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    SourceEqualityConstraintConstructors.top_cached (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le)
    trace ready available closed heap

end MicroCFTA.SourceEmptinessClassFields
