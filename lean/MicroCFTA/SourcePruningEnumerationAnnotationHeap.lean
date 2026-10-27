import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Normalized annotations in actual caller contexts

The current checked field invariant includes normalized stored equalities.
Actual completion producers retain that invariant in their returned context.
No separate final annotation premise is needed for their actual Post receipt.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialInvariant
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {caller : Caller width} {memos : Memos}

/-- The current loaded-field invariant derives normalized annotations at the same physical heap. -/
theorem Context.annotation_heap (initial : Context formulas solver inventory caller memos) :
    SourceEqualityAnnotationHeap.Heap
      (fun guard : Constraint => SourceEqualityGuardReadback.Cached guard.equalities)
      caller.checked.native.machine.heap := by
  intro key edge present
  exact (initial.ready.good.fields key edge present).1

/-- An actual Post receipt derives normalized annotations at its returned caller heap. -/
theorem Post.after_annotation_heap {next : Inventory} {before after : Caller width} {final : Memos}
    (post : Post formulas solver next before after final) :
    SourceEqualityAnnotationHeap.Heap
      (fun guard : Constraint => SourceEqualityGuardReadback.Cached guard.equalities)
      after.checked.native.machine.heap :=
  post.context.annotation_heap

end MicroCFTA.SourceCurrentAllocatedPartialInvariant
