import MicroCFTA.SourcePruningEnumerationInvocationEventLedger

namespace MicroCFTA.SourcePruningEnumerationInvocationEventLedger
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedInvocationTrace
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
local notation "TupleDone" => List Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "TupleStopped" => List Fragment → Observation width → Option Cached → Result Output Reason width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Result Output Reason width) →
  (Observation width → Option Cached → Result Output Reason width) → Result Output Reason width
set_option autoImplicit false

/- Note [The same lower-input event ledger]
Every original staged input has strict lower height than the parent.
Each guarded call therefore selects the same eager child.
The tuple callbacks agree on the actual remaining inputs.
The proof transports the existing child ledger and recurses on its same tail.
All events, paths, positions, endpoints and both indices stay unchanged.
A stopped tail remains stopped. No later sibling events are added.
No ledger is generated again from an output equality.
-/

private theorem ledger_children_members_congr (left right : Visitor) (inputs : List (Node × List Suspended)) :
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

private theorem ledger_children_guarded_eq_eager
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (parent : Node) (inputs : List (Node × List Suspended))
    (lower : ∀ child bucket, (child, bucket) ∈ inputs →
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent) :
    ∀ (done : TupleDone) (stopped : TupleStopped) (caller : Caller width) (before : Cached) (queries : Queries),
      visitChildren (runPolicy checkEmpty r n p h k edgesOf (.guarded parent))
        done stopped inputs caller before queries =
      visitChildren (runPolicy checkEmpty r n p h k edgesOf .eager)
        done stopped inputs caller before queries := by
  apply ledger_children_members_congr
  intro child bucket member caller before queries done stopped
  simp [runPolicy, lower child bucket member]

theorem children_eager_ledger_to_guarded
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (parent : Node) (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output) (exit : TupleExit width) (consumerIndex : Nat)
    (path : List Nat) (position : Nat) (events : List (Event width))
    (lower : ∀ child bucket, (child, bucket) ∈ inputs →
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent)
    (ledger : ChildrenLedgerAt checkEmpty r n p h k edgesOf .eager
      done stopped inputs caller before queries index output exit consumerIndex path position events) :
    ChildrenLedgerAt checkEmpty r n p h k edgesOf (.guarded parent)
      done stopped inputs caller before queries index output exit consumerIndex path position events
 := by
  revert lower ledger
  induction inputs generalizing done stopped caller before queries index output exit consumerIndex path position events with
  | nil =>
      intro _lower ledger
      cases ledger with
      | nil observed => exact .nil observed
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      intro lower ledger
      have headLower := lower incoming bucket List.mem_cons_self
      have restLower : ∀ child retained, (child, retained) ∈ rest →
          MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height parent := by
        intro child retained member
        exact lower child retained (List.mem_cons_of_mem (incoming, bucket) member)
      have tailSame := ledger_children_guarded_eq_eager
        (width := width) (Output := Output) (Reason := Reason)
        checkEmpty r n p h k edgesOf parent rest restLower
      cases ledger with
      | cons_done child tail =>
          refine .cons_done (.guarded_lower headLower ?_) ?_
          · simpa only [← tailSame] using child
          · apply ih
            · exact restLower
            · exact tail
      | cons_stopped child =>
          refine .cons_stopped (.guarded_lower headLower ?_)
          simpa only [← tailSame] using child

end MicroCFTA.SourcePruningEnumerationInvocationEventLedger

#check MicroCFTA.SourcePruningEnumerationInvocationEventLedger.children_eager_ledger_to_guarded
#print axioms MicroCFTA.SourcePruningEnumerationInvocationEventLedger.children_eager_ledger_to_guarded
