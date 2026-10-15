import MicroCFTA.SourceCurrentTargetPathComplete
import MicroCFTA.SourceCurrentMergedHeapEffects
import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.SourceEqualityNativeScopedCosts
import MicroCFTA.SourceEqualityAnnotationTarget

/-!
# Physical heaps through current shared target demands

Selected path domains derive closed projected operands. Actual projection,
merging, and scoped native calls retain stored unfolding costs and physical
edge annotations. Stored target hits have no heap effect. Unrelated ordinary
siblings can remain open. CostHeap does not bound execution time.
-/
namespace MicroCFTA.SourceCurrentTargetHeapEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityDemandTarget
open SourceEqualityProjectionPathDomain SourceEqualitySharedTargetState SourceEqualitySharedTargetForce SourceEqualitySharedTargetLeaf
open SourceEqualityAnnotationHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Actual captured-forest projection and merging retain stored costs on available open inputs. -/
theorem operand_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  cases trace with
  | force projection merged =>
      have first := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
      exact SourceCurrentMergedHeapEffects.merge_cost_heap merged (ready.advance _ first.1 first.2.1) first.2.2.2 first.2.2.1

/-- Actual first-seeded folds retain stored costs through every reached operand and native call. -/
theorem fold_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {seed : List Int} {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values)
    (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  induction trace with
  | nil seedDemand => exact operand_cost_heap seedDemand ready available costs
  | @cons path before value middle paths tail later result after operand rest step ih =>
      have first := operand.path_effects ready available (domains path (by simp))
      have firstCosts := operand_cost_heap operand ready available costs
      have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact domains _ List.mem_cons_self
        · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailAvailable : Values middle.machine.heap values := fun value member => first.2.1.available value (available value member)
      have remaining := rest.path_effects first.1 tailAvailable tailDomains
      exact step.cost_heap remaining.1 (ih first.1 tailAvailable tailDomains firstCosts)
        (remaining.2.1.available value first.2.2.1) remaining.2.2.1

/-- Every actual target retains stored costs without whole-forest closedness. -/
theorem target_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  cases trace with
  | nil => exact costs
  | cons actual => exact fold_cost_heap actual ready available domains costs

/-- First forcing retains actual target cost effects; stored receipt hits leave the heap unchanged. -/
theorem force_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (costs : CostHeap before.native.machine.heap) : CostHeap after.native.machine.heap := by
  cases trace with
  | hit => exact costs
  | miss _ actual =>
      exact target_cost_heap actual ready.native (fun value member => ready.captured.available value (known value member))
        (SourceCurrentTargetPathComplete.operand_domains record values domains path) costs

/-- A concrete leaf retains stored costs through its actual shared force and native request. -/
theorem leaf_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (member : path ∈ record.paths) (available : Available before.native.machine.heap input)
    (costs : CostHeap before.native.machine.heap) : CostHeap after.native.machine.heap := by
  cases trace with
  | apply forced step =>
      have first := forced.path_effects ready known domains member
      exact step.cost_heap first.1.native (force_cost_heap forced ready known domains costs)
        first.2.2.1 (first.2.1.available input available)

/-- A selected actual operand preserves arbitrary physical annotations through projection and merging. -/
theorem operand_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard} (topValid : annotation top)
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | force projection merged =>
      have first := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      exact SourceEqualityAnnotationTarget.merge annotation topValid merged (ready.advance _ first.1 first.2.1)
        first.2.2.1 first.2.2.2 (SourceEqualityProjectionPathDomain.forest_heap annotation projection ready.semantic available domain heap)

/-- Every actual source fold retains physical annotations through current selected path domains. -/
theorem fold_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {seed : List Int} {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  induction trace with
  | nil seedDemand => exact operand_heap annotation topValid seedDemand ready available (domains _ List.mem_cons_self) heap
  | @cons path before value middle paths tail later result after operand rest step ih =>
      have first := operand.path_effects ready available (domains path (by simp))
      have firstHeap := operand_heap annotation topValid operand ready available (domains path (by simp)) heap
      have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact domains _ List.mem_cons_self
        · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailAvailable : Values middle.machine.heap values := fun value member => first.2.1.available value (available value member)
      have remaining := rest.path_effects first.1 tailAvailable tailDomains
      exact SourceEqualityNativeAnnotationScoped.step annotation emptyValid conjoinedValid step remaining.1
        (remaining.2.1.available value first.2.2.1) remaining.2.2.1 (ih first.1 tailAvailable tailDomains firstHeap)

/-- Complete actual targets retain their physical annotation heap from the original path domains. -/
theorem target_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {paths : List (List Int)} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | nil => exact heap
  | cons actual => exact fold_heap annotation emptyValid conjoinedValid topValid actual ready available domains heap

/-- Target forcing retains physical annotations on both first construction and stored receipt reuse. -/
theorem force_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (heap : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases trace with
  | hit => exact heap
  | miss _ actual =>
      exact target_heap annotation emptyValid conjoinedValid topValid actual ready.native
        (fun value member => ready.captured.available value (known value member))
        (SourceCurrentTargetPathComplete.operand_domains record values domains path) heap

/-- A concrete shared leaf retains physical annotations through its exact force and native suffix. -/
theorem leaf_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (member : path ∈ record.paths) (available : Available before.native.machine.heap input)
    (heap : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases trace with
  | apply forced step =>
      have first := forced.path_effects ready known domains member
      exact SourceEqualityNativeAnnotationScoped.step annotation emptyValid conjoinedValid step first.1.native
        first.2.2.1 (first.2.1.available input available)
        (force_heap annotation emptyValid conjoinedValid topValid forced ready known domains heap)

end MicroCFTA.SourceCurrentTargetHeapEffects
