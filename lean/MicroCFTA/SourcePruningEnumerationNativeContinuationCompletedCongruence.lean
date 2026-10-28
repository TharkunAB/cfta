import MicroCFTA.SourcePruningEnumerationNativeContinuations

/-!
# Completed sibling scans under a changed hook

A completed scan invokes only completed hooks.
Agreement on those hook results retains the exact scan result.
The statement does not require agreement on stopped hooks.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Agreement on completed hook results retains the exact completed sibling scan. -/
theorem run_complete_congr
    (first second : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (same : ∀ fragment reached saved after outputs middleCaller middleQueries,
      first fragment reached saved after = .complete outputs middleCaller middleQueries →
      second fragment reached saved after = .complete outputs middleCaller middleQueries)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    ∀ processed outputs finalCaller finalQueries,
      run first checkEmpty r n p h k target scs before edges caller queries =
        .complete processed outputs finalCaller finalQueries →
      run second checkEmpty r n p h k target scs before edges caller queries =
        .complete processed outputs finalCaller finalQueries := by
  induction edges generalizing caller queries with
  | nil =>
      intro processed outputs finalCaller finalQueries actual
      simpa only [run] using actual
  | cons edge rest ih =>
      intro processed outputs finalCaller finalQueries actual
      cases observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs
          edge caller before queries with
      | none => simp only [run, observed, reduceCtorEq] at actual
      | some receipt =>
          cases receipt with
          | unhandled =>
              simp only [run, observed, SourcePruningEnumerationNativeBranches.advance, reduceCtorEq] at actual
          | complete fragment reached saved after =>
              cases continued : first fragment reached saved after with
              | stopped headOutputs reason endpoint =>
                  simp only [run, observed, continued, reduceCtorEq] at actual
              | complete headOutputs middleCaller middleQueries =>
                  have next := same fragment reached saved after headOutputs middleCaller middleQueries continued
                  cases following : run first checkEmpty r n p h k target scs before rest middleCaller middleQueries with
                  | stopped tailOutputs later current =>
                      simp only [run, observed, continued, following, reduceCtorEq] at actual
                  | complete tailProcessed later endCaller endQueries =>
                      have retained := ih middleCaller middleQueries tailProcessed later endCaller endQueries following
                      simp only [run, observed, continued, following] at actual
                      simpa only [run, observed, next, retained] using actual
          | rejected reached saved after =>
              cases following : run first checkEmpty r n p h k target scs before rest reached saved with
              | stopped tailProcessed later current =>
                  simp only [run, observed, SourcePruningEnumerationNativeBranches.advance,
                    following, reduceCtorEq] at actual
              | complete tailProcessed later endCaller endQueries =>
                  have retained := ih reached saved tailProcessed later endCaller endQueries following
                  simp only [run, observed, SourcePruningEnumerationNativeBranches.advance, following] at actual
                  simpa only [run, observed, SourcePruningEnumerationNativeBranches.advance, retained] using actual
          | stopped fragments observation candidate =>
              cases advanced : SourcePruningEnumerationNativeBranches.advance (.stopped fragments observation candidate) with
              | none => simp only [run, observed, advanced, reduceCtorEq] at actual
              | some endpoint =>
                  obtain ⟨reached, saved⟩ := endpoint
                  cases following : run first checkEmpty r n p h k target scs before rest reached saved with
                  | stopped tailProcessed later current =>
                      simp only [run, observed, advanced, following, reduceCtorEq] at actual
                  | complete tailProcessed later endCaller endQueries =>
                      have retained := ih reached saved tailProcessed later endCaller endQueries following
                      simp only [run, observed, advanced, following] at actual
                      simpa only [run, observed, advanced, retained] using actual

end MicroCFTA.SourcePruningEnumerationNativeContinuations
