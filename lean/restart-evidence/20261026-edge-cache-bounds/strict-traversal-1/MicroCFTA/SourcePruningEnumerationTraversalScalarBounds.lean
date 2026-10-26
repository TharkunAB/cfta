import MicroCFTA.SourcePruningEnumerationChildTraversal
import MicroCFTA.SourcePruningEnumerationChildScalarBounds

/-!
# Original scalar bounds for an actual ordered child traversal

Each child adds at most one slot and its incoming bucket length.
A stopped traversal retains the bound for its actual cache candidate.
The bounds do not assert that the remaining children execute.
-/
namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual complete and stopped caches satisfy the original list bounds at every fuel. -/
theorem observed_scalar_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries) :
    match run checkEmpty r n p h k inputs caller before queries with
    | .complete _ _ _ after =>
        after.core.counter ≤ before.core.counter + inputs.length ∧
          suspendedBound after.core ≤ suspendedBound before.core +
            (inputs.map fun input => input.2.length).sum
    | .stopped _ _ candidate =>
        ∀ after, candidate = some after →
          after.core.counter ≤ before.core.counter + inputs.length ∧
            suspendedBound after.core ≤ suspendedBound before.core +
              (inputs.map fun input => input.2.length).sum := by
  induction inputs generalizing caller before queries with
  | nil => simp only [run, List.length_nil, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl, and_self]
  | cons input rest ih =>
      rcases input with ⟨value, bucket⟩
      cases headEq : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k
          bucket value caller before queries with
      | mk observation candidate =>
          have stoppedHere : ∀ after, candidate = some after →
              after.core.counter ≤ before.core.counter + ((value, bucket) :: rest).length ∧
                suspendedBound after.core ≤ suspendedBound before.core +
                  (((value, bucket) :: rest).map fun input => input.2.length).sum := by
            intro after recovered
            have headBounds := SourcePruningEnumerationChildDispatch.observed_scalar_bounds
              checkEmpty r n p h k bucket value caller before queries after
              (by rw [headEq]; exact recovered)
            simp only [List.length_cons, List.map_cons, List.sum_cons]
            exact ⟨by omega, by omega⟩
          rcases observation with ⟨outcome, middleCaller, middleQueries, outer, waiting⟩
          cases outcome with
          | error fault => simpa only [run, headEq] using stoppedHere
          | ok returned =>
              cases returned with
              | none => simpa only [run, headEq] using stoppedHere
              | some raw =>
                  cases raw with
                  | nil => simpa only [run, headEq] using stoppedHere
                  | cons row rows =>
                      cases row with
                      | error fault => simpa only [run, headEq] using stoppedHere
                      | ok payload =>
                          rcases payload with ⟨fragment, returned⟩
                          cases rows with
                          | cons second remaining => simpa only [run, headEq] using stoppedHere
                          | nil =>
                              cases candidate with
                              | none => simpa only [run, headEq] using stoppedHere
                              | some middle =>
                                  have headBounds := SourcePruningEnumerationChildDispatch.observed_scalar_bounds
                                    checkEmpty r n p h k bucket value caller before queries middle
                                    (by rw [headEq])
                                  have tailBounds := ih middleCaller middle middleQueries
                                  cases tailEq : run checkEmpty r n p h k rest middleCaller middle middleQueries with
                                  | complete fragments finalCaller finalQueries final =>
                                      simp only [tailEq] at tailBounds
                                      simp only [run, headEq, tailEq, List.length_cons, List.map_cons, List.sum_cons]
                                      exact ⟨by omega, by omega⟩
                                  | stopped completedPrefix finalObservation finalCandidate =>
                                      simp only [tailEq] at tailBounds
                                      simp only [run, headEq, tailEq, List.length_cons, List.map_cons, List.sum_cons]
                                      intro after recovered
                                      have finalBounds := tailBounds after recovered
                                      exact ⟨by omega, by omega⟩

end MicroCFTA.SourcePruningEnumerationChildTraversal
