import MicroCFTA.SourceFlatPruningNativeContinuations

namespace MicroCFTA.SourceFlatPruningNativeContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Receipt" => SourceFlatPruningSelectedEdge.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual continued head supplies its outputs and native endpoint before the suffix. -/
theorem continued_head
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (n p h target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller middleCaller : Caller width) (queries middleQueries : Queries)
    (receipt : Receipt width) (outputs : List Output)
    (observed : SourceFlatPruningCapturedEdge.run checkEmpty n p h target scs edge caller before queries =
      some receipt)
    (continued : match (generalizing := false) receipt with
      | .complete fragment reached saved after =>
          hook fragment reached saved after = .complete outputs middleCaller middleQueries
      | _ => SourceFlatPruningNativeBranches.advance receipt = some (middleCaller, middleQueries) ∧
          outputs = []) :
    run hook checkEmpty n p h target scs before (edge :: rest) caller queries =
      match run hook checkEmpty n p h target scs before rest middleCaller middleQueries with
      | .complete processed later finalCaller finalQueries =>
          .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
      | .stopped processed later current =>
          .stopped (receipt :: processed) (outputs ++ later) current := by
  cases receipt with
  | complete fragment reached saved after =>
      exact completed_head hook checkEmpty n p h target scs before edge rest caller reached middleCaller
        queries saved middleQueries fragment after outputs observed continued
  | unhandled =>
      obtain ⟨impossible, _empty⟩ := continued
      cases impossible
  | rejected reached saved after =>
      obtain ⟨advanced, empty⟩ := continued
      subst outputs
      simp only [run, observed, advanced, List.nil_append]
      cases run hook checkEmpty n p h target scs before rest middleCaller middleQueries <;> rfl
  | stopped fragments observation candidate =>
      obtain ⟨advanced, empty⟩ := continued
      subst outputs
      simp only [run, observed, advanced, List.nil_append]
      cases run hook checkEmpty n p h target scs before rest middleCaller middleQueries <;> rfl

end MicroCFTA.SourceFlatPruningNativeContinuations
