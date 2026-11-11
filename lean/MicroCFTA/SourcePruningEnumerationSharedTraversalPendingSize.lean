import MicroCFTA.SourcePruningEnumerationSharedChildPendingSize

/-!
# Pending work through an actual shared child traversal

Each successful child charges at most its filled fragment's size.
The actual child result preserves alignment for the next child.
The complete trace therefore adds at most the sum of those sizes.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
open Language EnumerationState InternedConstructorTemplates EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem trace_pendingSize_le
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
    {fragments : List Fragment}
    (trace : Trace checkEmpty r n p h k inputs caller before queries fragments reached after saved)
    (assignment : Nat → Term Symbol) :
    before.core.counter = before.core.values.length →
      pendingSize after.core assignment ≤ pendingSize before.core assignment +
        (fragments.map (fun fragment => NumberedTerms.size (Fragments.fill assignment fragment))).sum := by
  induction trace with
  | nil => intro _aligned; simp
  | cons head _tail ih =>
      intro aligned
      have headBound := ChildDispatch.singleton_pendingSize_le
        (assignment := assignment) (aligned := aligned) (observed := head)
      have tailBound := ih (ChildDispatch.singleton_aligned aligned head)
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A complete actual traversal adds at most the sum of its filled child sizes. -/
theorem complete_pendingSize_le
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragments : List Fragment) (assignment : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (completed : run checkEmpty r n p h k inputs caller before queries =
      .complete fragments reached saved after) :
    pendingSize after.core assignment ≤ pendingSize before.core assignment +
      (fragments.map (fun fragment => NumberedTerms.size (Fragments.fill assignment fragment))).sum :=
  trace_pendingSize_le
    (complete_trace checkEmpty r n p h k inputs caller reached before after queries saved fragments completed)
    assignment aligned

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
