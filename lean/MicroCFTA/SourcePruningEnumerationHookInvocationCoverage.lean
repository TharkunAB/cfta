import MicroCFTA.SourcePruningEnumerationHookInvocation
import MicroCFTA.SourcePruningEnumerationContinuationHead

/-!
# Outputs from an actual hook invocation

Each actual invocation retains every output emitted by its hook.
The full sibling scan retains that same output after a later stop.
This statement does not assert that a hook emits an output.
-/
namespace MicroCFTA.SourcePruningEnumerationHookInvocation
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every output of an actual invoked hook remains in the full actual sibling result. -/
theorem Invocation.output_mem
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller queries
      fragment reached saved after) :
    ∀ output ∈ hookOutputs (hook fragment reached saved after),
      output ∈ foldOutputs (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
        target scs before edges caller queries) := by
  induction invocation with
  | @here edge rest caller queries fragment reached saved after observed =>
      intro output member
      cases callback : hook fragment reached saved after with
      | stopped outputs reason endpoint =>
          simpa only [SourcePruningEnumerationNativeContinuations.run, observed, callback,
            foldOutputs, hookOutputs] using member
      | complete outputs middleCaller middleQueries =>
          have first : output ∈ outputs := by
            simpa only [callback, hookOutputs] using member
          cases following : SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
              target scs before rest middleCaller middleQueries <;>
            simp only [SourcePruningEnumerationNativeContinuations.run, observed, callback,
              following, foldOutputs, List.mem_append]
          all_goals exact Or.inl first
  | @completed edge rest caller queries first headCaller headQueries headCache outputs
      middleCaller middleQueries fragment reached saved after observed continued tail ih =>
      intro output member
      have included := ih output member
      rw [SourcePruningEnumerationNativeContinuations.completed_head hook checkEmpty r n p h k
        target scs before edge rest caller headCaller middleCaller queries headQueries middleQueries
        first headCache outputs observed continued]
      cases following : SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
          target scs before rest middleCaller middleQueries <;>
        simp only [foldOutputs, List.mem_append]
      all_goals
        exact Or.inr (by simpa only [following, foldOutputs] using included)
  | @other edge rest caller queries receipt middleCaller middleQueries fragment reached saved after
      observed notComplete advanced tail ih =>
      intro output member
      have included := ih output member
      have continued : (match (generalizing := false) receipt with
        | .complete first headCaller headQueries headCache =>
            hook first headCaller headQueries headCache = .complete [] middleCaller middleQueries
        | _ => SourcePruningEnumerationNativeBranches.advance receipt = some (middleCaller, middleQueries) ∧
            ([] : List Output) = []) := by
        cases receipt with
        | complete _ _ _ _ => cases notComplete
        | unhandled | rejected _ _ _ | stopped _ _ _ => exact ⟨advanced, rfl⟩
      rw [SourcePruningEnumerationNativeContinuations.continued_head hook checkEmpty r n p h k
        target scs before edge rest caller middleCaller queries middleQueries receipt [] observed continued]
      cases following : SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
          target scs before rest middleCaller middleQueries <;>
        simpa only [following, foldOutputs, List.nil_append] using included

end MicroCFTA.SourcePruningEnumerationHookInvocation
