
import MicroCFTA.SourcePruningEnumerationNativeContinuations

namespace MicroCFTA.SourcePruningEnumerationNativeContinuations

open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Bound the processed alternatives by the original finite input list. -/
theorem run_original_alternatives_bound
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (before : Cached) (edges : List (EdgeValue Symbol Constraint))
    (caller : Caller width) (queries : Queries) :
    match run hook checkEmpty r n p h k target scs before edges caller queries with
    | .complete processed _outputs _finalCaller _finalQueries => processed.length = edges.length
    | .stopped processed _outputs _current => processed.length < edges.length
 := by
  induction edges generalizing caller queries with
  | nil => rfl
  | cons edge rest ih =>
      cases captured : SourcePruningEnumerationCapturedEdge.run
          checkEmpty r n p h k target scs edge caller before queries with
      | none =>
          simp only [run, captured, List.length_cons]
          exact Nat.zero_lt_succ _
      | some receipt =>
          cases receipt with
          | unhandled =>
              simp only [run, captured, SourcePruningEnumerationNativeBranches.advance, List.length_cons]
              exact Nat.zero_lt_succ _
          | rejected reached saved _after =>
              cases suffix : run hook checkEmpty r n p h k target scs before rest reached saved with
              | complete processed _outputs _finalCaller _finalQueries =>
                  have smaller : processed.length = rest.length := by
                    simpa only [suffix] using ih reached saved
                  simpa only [run, captured, SourcePruningEnumerationNativeBranches.advance,
                    suffix, List.length_cons] using congrArg Nat.succ smaller
              | stopped processed _outputs _current =>
                  have smaller : processed.length < rest.length := by
                    simpa only [suffix] using ih reached saved
                  simpa only [run, captured, SourcePruningEnumerationNativeBranches.advance,
                    suffix, List.length_cons] using Nat.succ_lt_succ smaller
          | stopped fragments observation candidate =>
              cases advanced : SourcePruningEnumerationNativeBranches.advance
                  (.stopped fragments observation candidate) with
              | none =>
                  simp only [run, captured, advanced, List.length_cons]
                  exact Nat.zero_lt_succ _
              | some endpoint =>
                  obtain ⟨middleCaller, middleQueries⟩ := endpoint
                  cases suffix : run hook checkEmpty r n p h k target scs before rest
                      middleCaller middleQueries with
                  | complete processed _outputs _finalCaller _finalQueries =>
                      have smaller : processed.length = rest.length := by
                        simpa only [suffix] using ih middleCaller middleQueries
                      simpa only [run, captured, advanced, suffix, List.length_cons]
                        using congrArg Nat.succ smaller
                  | stopped processed _outputs _current =>
                      have smaller : processed.length < rest.length := by
                        simpa only [suffix] using ih middleCaller middleQueries
                      simpa only [run, captured, advanced, suffix, List.length_cons]
                        using Nat.succ_lt_succ smaller
          | complete fragment reached saved after =>
              cases returned : hook fragment reached saved after with
              | stopped _outputs _reason _endpoint =>
                  simp only [run, captured, returned, List.length_cons]
                  exact Nat.zero_lt_succ _
              | complete _outputs middleCaller middleQueries =>
                  cases suffix : run hook checkEmpty r n p h k target scs before rest
                      middleCaller middleQueries with
                  | complete processed _later _finalCaller _finalQueries =>
                      have smaller : processed.length = rest.length := by
                        simpa only [suffix] using ih middleCaller middleQueries
                      simpa only [run, captured, returned, suffix, List.length_cons]
                        using congrArg Nat.succ smaller
                  | stopped processed _later _current =>
                      have smaller : processed.length < rest.length := by
                        simpa only [suffix] using ih middleCaller middleQueries
                      simpa only [run, captured, returned, suffix, List.length_cons]
                        using Nat.succ_lt_succ smaller

end MicroCFTA.SourcePruningEnumerationNativeContinuations
