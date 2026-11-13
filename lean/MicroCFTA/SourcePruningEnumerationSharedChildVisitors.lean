import MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation
import MicroCFTA.SourcePruningEnumerationSharedBranching

/-!
# Child callbacks on the existing shared path

A reached child invokes its callback before the remaining children run.
The selected-edge prefix and captured finalization use the existing workers.
The shallow adapter preserves the complete existing shared result.
This module adds no eager recursive policy or whole traversal claim.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedChildVisitors
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result HookResult advance endpoint)
open SourcePruningEnumerationSharedBranching (scan visitCaptured run_eq_scan)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Result Output Reason width) →
  (Observation width → Option Cached → Result Output Reason width) → Result Output Reason width

/-- Invoke the remaining children inside each actual child success callback. -/
noncomputable def visitChildren
    (visit : Visitor)
    (done : List Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : List Fragment → Observation width → Option Cached → Result Output Reason width) :
    List (Node × List Suspended) → Caller width → Cached → Queries → Result Output Reason width
  | [], caller, before, queries => done [] caller queries before
  | (value, bucket) :: rest, caller, before, queries =>
      visit bucket value caller before queries
        (fun fragment reached saved after =>
          visitChildren visit
            (fun fragments => done (fragment :: fragments))
            (fun completed => stopped (fragment :: completed)) rest reached after saved)
        (fun observation candidate => stopped [] observation candidate)

/-- Execute the actual own-class prefix and retain every selected-edge receipt. -/
noncomputable def visitSelected
    (visit : Visitor) (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    Result Output Reason width :=
  match SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => consume .unhandled
  | some [] => consume (.rejected caller queries before)
  | some [((symbol, staged, residual), middle)] =>
      visitChildren visit
        (fun fragments reached saved after =>
          let fragment := Fragments.Fragment.node symbol fragments
          consume (.complete fragment reached saved (SelectedEdge.finish residual fragment after)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
  | _ => consume .unhandled

private def finishReceipt
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (caller : Caller width) (queries : Queries) (receipt : Receipt width) : Result Output Reason width :=
  match receipt with
  | .complete fragment reached saved after =>
      match hook fragment reached saved after with
      | .stopped outputs reason reachedEndpoint =>
          .stopped [] outputs (.continuation receipt reason reachedEndpoint)
      | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
  | other =>
      match advance other with
      | none => .stopped [] [] (.edge (some other) (endpoint other caller queries))
      | some (reached, saved) => .complete [other] [] reached saved

/-- Finalize only the captured selected target and retain the exact hook outcome. -/
noncomputable def visitCapturedWith
    (visit : Visitor)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (k target : Nat) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (queries : Queries) (before : Cached) : Result Output Reason width :=
  visitSelected visit (fun receipt =>
    match receipt with
    | .complete fragment reached saved after =>
        match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
        | some finished => finishReceipt hook caller queries (.complete fragment reached saved finished)
        | none => finishReceipt hook caller queries (.finalizeStopped fragment reached saved after)
    | other => finishReceipt hook caller queries other) scs edge caller before queries

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Execute the existing shallow dispatch and invoke the matching actual callback. -/
noncomputable def shallowVisit
    (checkEmpty : Bool) (r n p h k : Nat)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : Observation width → Option Cached → Result Output Reason width) : Result Output Reason width :=
  match ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries with
  | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
      done fragment reached saved after
  | (observation, candidate) => stopped observation candidate

/-- The shallow child callbacks retain the entire original traversal outcome. -/
theorem visitChildren_shallow
    (checkEmpty : Bool) (r n p h k : Nat)
    (done : List Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : List Fragment → Observation width → Option Cached → Result Output Reason width)
    (inputs : List (Node × List Suspended)) (caller : Caller width) (before : Cached) (queries : Queries) :
    visitChildren (shallowVisit checkEmpty r n p h k) done stopped inputs caller before queries =
      match ChildTraversal.run checkEmpty r n p h k inputs caller before queries with
      | .complete fragments reached saved after => done fragments reached saved after
      | .stopped completed observation candidate => stopped completed observation candidate := by
  induction inputs generalizing caller before queries done stopped with
  | nil => rfl
  | cons input rest ih =>
      rcases input with ⟨value, bucket⟩
      cases headEq : ChildDispatch.run checkEmpty r n p h k bucket value caller before queries with
      | mk observation candidate =>
          rcases observation with ⟨outcome, reached, saved, _outer, _waiting⟩
          cases outcome with
          | error fault => simp only [visitChildren, shallowVisit, ChildTraversal.run, headEq]
          | ok returned =>
              cases returned with
              | none => simp only [visitChildren, shallowVisit, ChildTraversal.run, headEq]
              | some raw =>
                  cases raw with
                  | nil => simp only [visitChildren, shallowVisit, ChildTraversal.run, headEq]
                  | cons row rows =>
                      cases row with
                      | error fault => simp only [visitChildren, shallowVisit, ChildTraversal.run, headEq]
                      | ok child =>
                          rcases child with ⟨fragment, _returnedCore⟩
                          cases rows with
                          | cons row rows => simp only [visitChildren, shallowVisit, ChildTraversal.run, headEq]
                          | nil =>
                              cases candidate with
                              | none => simp only [visitChildren, shallowVisit, ChildTraversal.run, headEq]
                              | some after =>
                                  simp only [visitChildren, shallowVisit, ChildTraversal.run, headEq]
                                  rw [ih]
                                  cases ChildTraversal.run checkEmpty r n p h k rest reached after saved <;> rfl

/-- Every selected-edge case reaches the same executed receipt consumer. -/
theorem visitSelected_shallow
    (checkEmpty : Bool) (r n p h k : Nat)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    visitSelected (shallowVisit checkEmpty r n p h k) consume scs edge caller before queries =
      consume (SelectedEdge.run checkEmpty r n p h k scs edge caller before queries) := by
  cases prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => simp only [visitSelected, SelectedEdge.run, prepared]
  | some rows =>
      cases rows with
      | nil => simp only [visitSelected, SelectedEdge.run, prepared]
      | cons first rest =>
          cases rest with
          | cons second rest => simp only [visitSelected, SelectedEdge.run, prepared]
          | nil =>
              rcases first with ⟨⟨symbol, staged, residual⟩, middle⟩
              simp only [visitSelected, SelectedEdge.run, prepared]
              rw [visitChildren_shallow]
              cases ChildTraversal.run checkEmpty r n p h k
                (staged.map (fun input => (input.1, input.2.1))) caller middle queries <;> rfl

/-- The shallow captured adapter preserves the complete existing shared result. -/
theorem visitCapturedWith_shallow
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : Edge) (caller : Caller width) (queries : Queries) (before : Cached) :
    visitCapturedWith (shallowVisit checkEmpty r n p h k) hook k target scs edge caller queries before =
      visitCaptured hook checkEmpty r n p h k target scs edge caller queries before := by
  rw [visitCapturedWith, visitSelected_shallow]
  cases observed : SelectedEdge.run checkEmpty r n p h k scs edge caller before queries <;>
    simp only [visitCaptured, CapturedEdge.run, observed]
  all_goals first | rfl | (split <;> simp_all only [finishReceipt] <;> rfl)

/-- Rewrite the actual old worker into this callback path at the shallow policy. -/
theorem run_eq_scan_shallow
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List Edge) (caller : Caller width) (queries : Queries) :
    NativeContinuations.run hook checkEmpty r n p h k target scs before edges caller queries =
      scan (visitCapturedWith (shallowVisit checkEmpty r n p h k) hook k target scs)
        before edges caller queries := by
  rw [run_eq_scan]
  apply congrArg (fun (visit : Edge → Caller width → Queries → Cached → Result Output Reason width) =>
    scan visit before edges caller queries)
  funext edge reached saved after
  exact (visitCapturedWith_shallow hook checkEmpty r n p h k target scs edge reached saved after).symm

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- Expose captured finalization through the public receipt continuation. -/
theorem visitCapturedWith_eq_receipts
    (visit : Visitor)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (k target : Nat) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    visitCapturedWith visit hook k target scs edge caller queries before =
      visitSelected visit (fun receipt =>
        match receipt with
        | .complete fragment reached saved after =>
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
                (some (.complete fragment reached saved finished))
            | none => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
                (some (.finalizeStopped fragment reached saved after))
        | other => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some other))
        scs edge caller before queries := by
  have same (receipt : Receipt width) :
      finishReceipt hook caller queries receipt =
        SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some receipt) := by
    cases receipt with
    | complete fragment reached saved after =>
        cases called : hook fragment reached saved after <;>
          simp only [finishReceipt, SourcePruningEnumerationSharedReceiptContinuation.run, called]
    | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ => rfl
  unfold visitCapturedWith
  simp only [same]

end MicroCFTA.SourcePruningEnumerationSharedChildVisitors
