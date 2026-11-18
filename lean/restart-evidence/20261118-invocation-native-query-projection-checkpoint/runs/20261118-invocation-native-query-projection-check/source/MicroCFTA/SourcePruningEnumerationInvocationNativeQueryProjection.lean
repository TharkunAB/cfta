import MicroCFTA.SourcePruningEnumerationInvocationEventLedger
import MicroCFTA.SourcePruningEnumerationSharedChildDispatchQueryEvents

/-!
# Indexed native queries of one causal operation ledger

Note [One operation list supplies query origins]
The projection preserves operation order and each dispatch query list.
Preparation and residual operations contribute no entries to this projection.
One list lookup supplies the operation occurrence and its local query index.
Authenticity identifies its recorded result with the same literal child run.
Observer exactness then identifies that complete result and optional cache.
No independent ledger is selected through a shared Prop proof index.

The global query index equals the projected earlier-operation length plus the
local query index. This statement preserves duplicate occurrences. It does not
claim that path tags, operation values or local indices are globally unique.
The given causal ledger does not describe every eager-worker query or callback.
-/

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationInvocationNativeQueryProjection
open EnumerationState (Suspended)
open InternedConstructorTemplates (Value EdgeKey)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Observation" => SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation
local notation "Operation" => SourcePruningEnumerationInvocationEventLedger.Event
local notation "QueryEvent" => SourcePruningEnumerationSharedDispatchQueryEvents.Event
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Flatten actual dispatch query lists in the given operation order. -/
noncomputable def nativeQueries (operations : List (Operation width)) : List (QueryEvent width)
 :=
  operations.flatMap fun operation =>
    match operation with
    | .prepare _ _ _ _ _ _ _ => []
    | .residual _ _ _ _ _ _ _ => []
    | .dispatch _ checkEmpty r n p h k scs incoming caller before queries _ _ =>
        (SourcePruningEnumerationSharedChildDispatchQueryEvents.observe
          checkEmpty r n p h k scs incoming caller before queries).2

/-- An indexed projected query retains one authentic dispatch occurrence and local index. -/
theorem native_query_origin
    (operations : List (Operation width))
    (authentic : ∀ operation ∈ operations,
      SourcePruningEnumerationInvocationEventLedger.AuthenticEvent operation)
    (nativeIndex : Nat) (queryEvent : QueryEvent width)
    (found : (nativeQueries operations)[nativeIndex]? = some queryEvent) :
    ∃ (operationIndex : Nat) (path : List Nat) (checkEmpty : Bool) (r n p h k : Nat)
        (scs : List Suspended) (incoming : Node) (caller : Caller width)
        (before : Cached) (queries : Queries) (recorded : Observation width)
        (candidate : Option Cached) (localIndex : Nat),
      operations[operationIndex]? = some (.dispatch path checkEmpty r n p h k
        scs incoming caller before queries recorded candidate) ∧
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
        checkEmpty r n p h k scs incoming caller before queries = (recorded, candidate) ∧
      (SourcePruningEnumerationSharedChildDispatchQueryEvents.observe
        checkEmpty r n p h k scs incoming caller before queries).1 = (recorded, candidate) ∧
      ((SourcePruningEnumerationSharedChildDispatchQueryEvents.observe
        checkEmpty r n p h k scs incoming caller before queries).2)[localIndex]? = some queryEvent ∧
      nativeIndex = (nativeQueries (operations.take operationIndex)).length + localIndex
 := by
  let piece : Operation width → List (QueryEvent width) := fun operation =>
    match operation with
    | .prepare _ _ _ _ _ _ _ => []
    | .residual _ _ _ _ _ _ _ => []
    | .dispatch _ checkEmpty r n p h k scs incoming caller before queries _ _ =>
        (SourcePruningEnumerationSharedChildDispatchQueryEvents.observe
          checkEmpty r n p h k scs incoming caller before queries).2
  have indexed : ∀ (values : List (Operation width)) (index : Nat),
      (values.flatMap piece)[index]? = some queryEvent →
      ∃ outer selected inner,
        values[outer]? = some selected ∧ (piece selected)[inner]? = some queryEvent ∧
        index = ((values.take outer).flatMap piece).length + inner := by
    intro values index observed
    induction values generalizing index with
    | nil =>
        simp only [List.flatMap_nil, List.getElem?_nil] at observed
        cases observed
    | cons first rest ih =>
        simp only [List.flatMap_cons] at observed
        by_cases short : index < (piece first).length
        · rw [List.getElem?_append_left short] at observed
          exact ⟨0, first, index, rfl, observed, by
            simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add]⟩
        · have long : (piece first).length ≤ index := by omega
          rw [List.getElem?_append_right long] at observed
          obtain ⟨outer, selected, inner, atOuter, atInner, offset⟩ :=
            ih (index - (piece first).length) observed
          refine ⟨outer + 1, selected, inner, atOuter, atInner, ?_⟩
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          omega
  change (operations.flatMap piece)[nativeIndex]? = some queryEvent at found
  obtain ⟨operationIndex, operation, localIndex, atOperation, atQuery, offset⟩ :=
    indexed operations nativeIndex found
  have authenticSelected := authentic operation (List.mem_of_getElem? atOperation)
  cases operation with
  | prepare path scs edge caller before queries rows =>
      simp only [piece, List.getElem?_nil] at atQuery
      cases atQuery
  | residual path guard fragment caller queries before after =>
      simp only [piece, List.getElem?_nil] at atQuery
      cases atQuery
  | dispatch path checkEmpty r n p h k scs incoming caller before queries recorded candidate =>
      have ran : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
          checkEmpty r n p h k scs incoming caller before queries = (recorded, candidate) :=
        authenticSelected
      refine ⟨operationIndex, path, checkEmpty, r, n, p, h, k, scs, incoming, caller,
        before, queries, recorded, candidate, localIndex, atOperation, ran, ?_, atQuery, offset⟩
      exact (SourcePruningEnumerationSharedChildDispatchQueryEvents.observe_exact
        checkEmpty r n p h k scs incoming caller before queries).trans ran

end MicroCFTA.SourcePruningEnumerationInvocationNativeQueryProjection

#check MicroCFTA.SourcePruningEnumerationInvocationNativeQueryProjection.nativeQueries
#print axioms MicroCFTA.SourcePruningEnumerationInvocationNativeQueryProjection.native_query_origin
