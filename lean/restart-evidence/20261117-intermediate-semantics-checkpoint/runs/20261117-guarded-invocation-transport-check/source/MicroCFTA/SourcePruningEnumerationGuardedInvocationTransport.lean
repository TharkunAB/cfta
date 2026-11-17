import MicroCFTA.SourcePruningEnumerationSharedInvocationTrace

namespace MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Observation" => ChildDispatch.Observation
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Done" => List Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "Stopped" => List Fragment → Observation width → Option Cached → Result Output Reason width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Result Output Reason width) →
  (Observation width → Option Cached → Result Output Reason width) → Result Output Reason width
set_option autoImplicit false

/- Note [Lower staged inputs select the same eager invocation]
Every original input satisfies the strict parent-height bound.
Each guarded child therefore uses its existing eager trace.
The remaining literal tuple callback is equal on the actual remaining inputs.
The proof transports that same child and tail derivation.
It does not create a trace from output equality.
All callback arguments, native/cache/query endpoints and both indices stay fixed.
There is no Canonical, Packet, model or future callback premise.
-/

private theorem children_members_congr (left right : Visitor) (inputs : List (Node × List Suspended)) :
    (∀ child bucket, (child, bucket) ∈ inputs → ∀ caller before queries done stopped,
      left bucket child caller before queries done stopped = right bucket child caller before queries done stopped) →
    ∀ done stopped caller before queries,
      visitChildren left done stopped inputs caller before queries =
        visitChildren right done stopped inputs caller before queries := by
  induction inputs with
  | nil => intro _ _ _ _ _ _; rfl
  | cons input rest ih =>
      rcases input with ⟨child, bucket⟩
      intro same done stopped caller before queries
      simp only [visitChildren]
      rw [same child bucket (by simp)]
      apply congrArg (fun yes => right bucket child caller before queries yes
        (fun observation candidate => stopped [] observation candidate))
      funext fragment reached saved after
      exact ih (fun value retained member => same value retained (List.mem_cons_of_mem _ member))
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) reached after saved

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem children_guarded_eq_eager
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (parent : Node) (inputs : List (Node × List Suspended))
    (lower : ∀ child bucket, (child, bucket) ∈ inputs →
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent) :
    ∀ (done : Done) (stopped : Stopped) (caller : Caller width) (before : Cached) (queries : Queries),
      visitChildren (runPolicy checkEmpty r n p h k edgesOf (.guarded parent))
        done stopped inputs caller before queries =
      visitChildren (runPolicy checkEmpty r n p h k edgesOf .eager)
        done stopped inputs caller before queries := by
  apply children_members_congr
  intro child bucket member caller before queries done stopped
  simp [runPolicy, lower child bucket member]

private theorem child_guarded_to_eager
    {checkEmpty : Bool} {r n p h k : Nat} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {parent incoming : Node} {scs : List Suspended} {caller : Caller width}
    {before : Cached} {queries : Queries}
    {done : Fragment → Caller width → Queries → Cached → Result Output Reason width}
    {stopped : Observation width → Option Cached → Result Output Reason width}
    {index : Nat} {output : Output} {exit : ChildExit width} {consumerIndex : Nat}
    (lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf (.guarded parent)
      scs incoming caller before queries done stopped index output exit consumerIndex) :
    ChildInvocationAt checkEmpty r n p h k edgesOf .eager
      scs incoming caller before queries done stopped index output exit consumerIndex := by
  cases trace with
  | guarded_lower _ child => exact child
  | guarded_else contrary _child => exact (contrary lower).elim

theorem children_guarded_to_eager
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (parent : Node) (done : Done) (stopped : Stopped) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output) (exit : TupleExit width) (consumerIndex : Nat)
    (lower : ∀ child bucket, (child, bucket) ∈ inputs →
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent)
    (trace : ChildrenInvocationAt checkEmpty r n p h k edgesOf (.guarded parent)
      done stopped inputs caller before queries index output exit consumerIndex) :
    ChildrenInvocationAt checkEmpty r n p h k edgesOf .eager
      done stopped inputs caller before queries index output exit consumerIndex
 := by
  revert lower trace
  induction inputs generalizing done stopped caller before queries index output exit consumerIndex with
  | nil =>
      intro _lower trace
      cases trace with
      | nil observed => exact .nil observed
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      intro lower trace
      have headLower := lower incoming bucket List.mem_cons_self
      have restLower : ∀ child retained, (child, retained) ∈ rest →
          MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent := by
        intro child retained member
        exact lower child retained (List.mem_cons_of_mem (incoming, bucket) member)
      have tailSame := children_guarded_eq_eager checkEmpty r n p h k edgesOf parent rest restLower
      cases trace with
      | cons_done child tail =>
          have eagerChild := child_guarded_to_eager headLower child
          simp only [tailSame] at eagerChild
          exact .cons_done eagerChild (ih _ _ _ _ _ _ _ _ _ restLower tail)
      | cons_stopped child =>
          have eagerChild := child_guarded_to_eager headLower child
          simp only [tailSame] at eagerChild
          exact .cons_stopped eagerChild

end MicroCFTA.SourcePruningEnumerationSharedInvocationTrace

#check MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.children_guarded_to_eager
#print axioms MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.children_guarded_to_eager
