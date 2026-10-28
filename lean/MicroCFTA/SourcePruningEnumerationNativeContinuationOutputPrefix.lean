import MicroCFTA.SourcePruningEnumerationHookInvocation
import MicroCFTA.SourcePruningEnumerationContinuationHead

/-!
# Ordered output prefixes under extended hooks

Completed hooks retain their exact outputs and native endpoint.
Stopped hooks can extend their output list.
The actual sibling scan retains its complete original output prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeContinuations
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationHookInvocation (hookOutputs foldOutputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem continued_outputs
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller middleCaller : Caller width) (queries middleQueries : Queries)
    (receipt : Receipt width) (outputs : List Output)
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      some receipt)
    (continued : match (generalizing := false) receipt with
      | .complete fragment reached saved after =>
          hook fragment reached saved after = .complete outputs middleCaller middleQueries
      | _ => SourcePruningEnumerationNativeBranches.advance receipt = some (middleCaller, middleQueries) ∧
          outputs = []) :
    foldOutputs (run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries) =
      outputs ++ foldOutputs (run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries) := by
  rw [continued_head hook checkEmpty r n p h k target scs before edge rest caller middleCaller queries
    middleQueries receipt outputs observed continued]
  cases run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries <;> rfl

/-- Completed hook agreement and hook output extension retain the whole actual scan output prefix. -/
theorem run_outputs_prefix
    (first second : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (same : ∀ fragment reached saved after outputs middleCaller middleQueries,
      first fragment reached saved after = .complete outputs middleCaller middleQueries →
      second fragment reached saved after = .complete outputs middleCaller middleQueries)
    (prefixHooks : ∀ fragment reached saved after,
      List.IsPrefix (hookOutputs (first fragment reached saved after))
        (hookOutputs (second fragment reached saved after)))
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    List.IsPrefix (foldOutputs (run first checkEmpty r n p h k target scs before edges caller queries))
      (foldOutputs (run second checkEmpty r n p h k target scs before edges caller queries)) := by
  induction edges generalizing caller queries with
  | nil => exact List.prefix_rfl
  | cons edge rest ih =>
      cases observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none =>
          simp only [run, observed, foldOutputs]
          exact List.prefix_rfl
      | some receipt =>
          cases receipt with
          | unhandled =>
              simp only [run, observed, SourcePruningEnumerationNativeBranches.advance, foldOutputs]
              exact List.prefix_rfl
          | complete fragment reached saved after =>
              cases continued : first fragment reached saved after with
              | complete outputs middleCaller middleQueries =>
                  have next := same fragment reached saved after outputs middleCaller middleQueries continued
                  rw [continued_outputs first checkEmpty r n p h k target scs before edge rest caller middleCaller
                      queries middleQueries (.complete fragment reached saved after) outputs observed continued,
                    continued_outputs second checkEmpty r n p h k target scs before edge rest caller middleCaller
                      queries middleQueries (.complete fragment reached saved after) outputs observed next]
                  exact (List.prefix_append_right_inj outputs).mpr (ih middleCaller middleQueries)
              | stopped outputs reason endpoint =>
                  have retained := prefixHooks fragment reached saved after
                  cases next : second fragment reached saved after with
                  | stopped later newReason newEndpoint =>
                      simpa only [run, observed, continued, next, hookOutputs, foldOutputs] using retained
                  | complete later middleCaller middleQueries =>
                      have headPrefix : List.IsPrefix outputs later := by
                        simpa only [continued, next, hookOutputs] using retained
                      rw [continued_outputs second checkEmpty r n p h k target scs before edge rest caller middleCaller
                        queries middleQueries (.complete fragment reached saved after) later observed next]
                      simp only [run, observed, continued, foldOutputs]
                      exact List.prefix_append_of_prefix headPrefix
          | rejected reached saved after =>
              rw [continued_outputs first checkEmpty r n p h k target scs before edge rest caller reached queries saved
                  (.rejected reached saved after) [] observed ⟨rfl, rfl⟩,
                continued_outputs second checkEmpty r n p h k target scs before edge rest caller reached queries saved
                  (.rejected reached saved after) [] observed ⟨rfl, rfl⟩]
              simpa only [List.nil_append] using ih reached saved
          | stopped fragments observation candidate =>
              cases advanced : SourcePruningEnumerationNativeBranches.advance (.stopped fragments observation candidate) with
              | none =>
                  simp only [run, observed, advanced, foldOutputs]
                  exact List.prefix_rfl
              | some endpoint =>
                  obtain ⟨reached, saved⟩ := endpoint
                  rw [continued_outputs first checkEmpty r n p h k target scs before edge rest caller reached queries saved
                      (.stopped fragments observation candidate) [] observed ⟨advanced, rfl⟩,
                    continued_outputs second checkEmpty r n p h k target scs before edge rest caller reached queries saved
                      (.stopped fragments observation candidate) [] observed ⟨advanced, rfl⟩]
                  simpa only [List.nil_append] using ih reached saved

end MicroCFTA.SourcePruningEnumerationNativeContinuations
