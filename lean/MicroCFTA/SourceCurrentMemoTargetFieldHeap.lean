import MicroCFTA.SourceCurrentMemoMergeFieldHeap
import MicroCFTA.SourceCurrentMemoSharedTargetLeaf
import MicroCFTA.SourceEqualityNativeAnnotationScoped

/-!
# Physical annotations through memo-aware shared targets and leaves

Projection uses only selected path domains. Each actual completed merge
retains annotations. Native intersection checks its emitted guards.
Stored target hits retain the heap without a new request.
-/
namespace MicroCFTA.SourceCurrentMemoTargetFieldHeap
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoTargetOperand SourceCurrentMemoDemandTarget
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetForce SourceCurrentMemoSharedTargetLeaf
open SourceEqualityAnnotationHeap (Heap)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

/-- Actual projection and completed memo-aware merging preserve physical edge annotations. -/
theorem operand_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard} (topValid : annotation top)
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (fields : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | force projection merged =>
      have first := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
      exact SourceCurrentMemoMergeFieldHeap.native_heap annotation topValid merged (ready.advance _ first.1 first.2.1)
        physical.2.2.1 (stored.grows first.1) first.2.2.1
        (SourceEqualityProjectionPathDomain.forest_heap annotation projection ready.semantic available domain fields)

/-- Every fold prefix derives its annotation heap at the actual returned native state. -/
theorem fold_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {seed : List Int} {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values)
    (fields : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  induction trace with
  | nil operand => exact operand_heap annotation topValid operand ready costs stored available (domains _ List.mem_cons_self) fields
  | cons operand rest step ih =>
      have first := operand.effects ready costs stored available (domains _ (by simp))
      have firstFields := operand_heap annotation topValid operand ready costs stored available (domains _ (by simp)) fields
      have tailDomains := tail_all domains
      have tailAvailable : Values _ values := fun value member => first.keeps.available value (available value member)
      have remaining := rest.effects first.ready first.costs first.stored tailAvailable tailDomains
      exact SourceEqualityNativeAnnotationScoped.step annotation emptyValid conjoinedValid step remaining.ready
        (remaining.keeps.available _ first.available) remaining.available
        (ih first.ready first.costs first.stored tailAvailable tailDomains firstFields)

/-- Complete targets derive their annotation heap from the original selected path domains. -/
theorem target_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (fields : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | nil => exact fields
  | cons fold => exact fold_heap annotation emptyValid conjoinedValid topValid fold ready costs stored available domains fields

/-- First forcing derives fields through the actual target; slot hits retain the current heap. -/
theorem force_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : SourceCurrentMemoSharedTargetState.State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (fields : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases trace with
  | hit => exact fields
  | miss _ actual =>
      exact target_heap annotation emptyValid conjoinedValid topValid actual ready.native ready.costs ready.stored
        (fun value member => ready.captured.available value (known value member))
        (SourceCurrentTargetPathComplete.operand_domains record values domains path) fields

/-- Each leaf retains annotations through its actual force and native intersection. -/
theorem leaf_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : SourceCurrentMemoSharedTargetState.State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (member : path ∈ record.paths) (available : Available before.native.machine.heap input)
    (fields : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known domains member
      exact SourceEqualityNativeAnnotationScoped.step annotation emptyValid conjoinedValid step first.1.native
        first.2.2.1 (first.2.1.available input available)
        (force_heap annotation emptyValid conjoinedValid topValid forced ready known domains fields)

end MicroCFTA.SourceCurrentMemoTargetFieldHeap
