import MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations

/-!
# Actual hook invocations behind emitted outputs

Each invocation retains the captured cache and the actual native endpoints.
Earlier completed hooks supply the caller used by the next sibling.
Outputs before a later stop retain the same invocation certificate.
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
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "FoldResult" => SourcePruningEnumerationNativeContinuations.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- Retain outputs from complete and stopped hooks. -/
def hookOutputs : HookResult Output Reason width → List Output
  | .complete outputs _ _ => outputs
  | .stopped outputs _ _ => outputs

/-- Retain outputs from complete and stopped alternative scans. -/
def foldOutputs : FoldResult Output Reason width → List Output
  | .complete _ outputs _ _ => outputs
  | .stopped _ outputs _ => outputs

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Record the actual captured edge and each earlier sibling endpoint. -/
inductive Invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached) :
    List (EdgeValue Symbol Constraint) → Caller width → Queries →
      Fragment → Caller width → Queries → Cached → Prop where
  /-- The first edge completes at the recorded hook input. -/
  | here {edge rest caller queries fragment reached saved after}
      (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
        some (.complete fragment reached saved after)) :
      Invocation hook checkEmpty r n p h k target scs before (edge :: rest) caller queries
        fragment reached saved after
  /-- A completed hook supplies the actual native endpoint of the suffix. -/
  | completed {edge rest caller queries first headCaller headQueries headCache outputs middleCaller middleQueries
        fragment reached saved after}
      (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
        some (.complete first headCaller headQueries headCache))
      (continued : hook first headCaller headQueries headCache = .complete outputs middleCaller middleQueries)
      (tail : Invocation hook checkEmpty r n p h k target scs before rest middleCaller middleQueries
        fragment reached saved after) :
      Invocation hook checkEmpty r n p h k target scs before (edge :: rest) caller queries
        fragment reached saved after
  /-- A handled receipt without a completed fragment advances only native state. -/
  | other {edge rest caller queries receipt middleCaller middleQueries fragment reached saved after}
      (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
        some receipt)
      (notComplete : match receipt with | .complete .. => False | _ => True)
      (advanced : SourcePruningEnumerationNativeBranches.advance receipt = some (middleCaller, middleQueries))
      (tail : Invocation hook checkEmpty r n p h k target scs before rest middleCaller middleQueries
        fragment reached saved after) :
      Invocation hook checkEmpty r n p h k target scs before (edge :: rest) caller queries
        fragment reached saved after

/-- Every emitted scan output comes from a literal hook invocation on its actual path. -/
theorem run_output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    ∀ output ∈ foldOutputs (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
      target scs before edges caller queries),
      ∃ fragment reached saved after,
        Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after ∧
        output ∈ hookOutputs (hook fragment reached saved after) := by
  induction edges generalizing caller queries with
  | nil => intro output member; cases member
  | cons edge rest ih =>
      cases observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none =>
          intro output member
          simp only [SourcePruningEnumerationNativeContinuations.run, observed, foldOutputs, List.not_mem_nil] at member
      | some receipt =>
          cases receipt with
          | unhandled =>
              intro output member
              simp only [SourcePruningEnumerationNativeContinuations.run, observed,
                SourcePruningEnumerationNativeBranches.advance, foldOutputs, List.not_mem_nil] at member
          | rejected reached saved after =>
              have suffix := ih reached saved
              cases following : SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
                  target scs before rest reached saved <;>
                intro output member
              all_goals
                have listed := member
                simp only [SourcePruningEnumerationNativeContinuations.run, observed,
                  SourcePruningEnumerationNativeBranches.advance, following, foldOutputs] at listed
                rw [following] at suffix
                obtain ⟨fragment, actual, current, cache, origin, emitted⟩ := suffix output listed
                exact ⟨fragment, actual, current, cache, .other observed trivial rfl origin, emitted⟩
          | complete fragment reached saved after =>
              cases callback : hook fragment reached saved after with
              | stopped outputs reason endpoint =>
                  intro output member
                  refine ⟨fragment, reached, saved, after, .here observed, ?_⟩
                  simpa only [SourcePruningEnumerationNativeContinuations.run, observed, callback,
                    foldOutputs, hookOutputs] using member
              | complete outputs middleCaller middleQueries =>
                  have suffix := ih middleCaller middleQueries
                  cases following : SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
                      target scs before rest middleCaller middleQueries <;>
                    intro output member
                  all_goals
                    have listed : output ∈ outputs ++ _ := by
                      simpa only [SourcePruningEnumerationNativeContinuations.run, observed, callback,
                        following, foldOutputs] using member
                    rcases List.mem_append.mp listed with head | tail
                    · exact ⟨fragment, reached, saved, after, .here observed, by
                        simpa only [callback, hookOutputs] using head⟩
                    · rw [following] at suffix
                      obtain ⟨nextFragment, actual, current, cache, origin, emitted⟩ := suffix output tail
                      exact ⟨nextFragment, actual, current, cache, .completed observed callback origin, emitted⟩
          | stopped fragments observation candidate =>
              cases advanced : SourcePruningEnumerationNativeBranches.advance (.stopped fragments observation candidate) with
              | none =>
                  intro output member
                  simp only [SourcePruningEnumerationNativeContinuations.run, observed, advanced,
                    foldOutputs, List.not_mem_nil] at member
              | some endpoint =>
                  obtain ⟨middleCaller, middleQueries⟩ := endpoint
                  have suffix := ih middleCaller middleQueries
                  cases following : SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
                      target scs before rest middleCaller middleQueries <;>
                    intro output member
                  all_goals
                    have listed := member
                    simp only [SourcePruningEnumerationNativeContinuations.run, observed, advanced,
                      following, foldOutputs] at listed
                    rw [following] at suffix
                    obtain ⟨fragment, actual, current, cache, origin, emitted⟩ := suffix output listed
                    exact ⟨fragment, actual, current, cache, .other observed trivial advanced origin, emitted⟩

/-- An invocation identifies a selected edge at its own actual native caller. -/
theorem Invocation.selected
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after) :
    ∃ edge ∈ edges, ∃ headCaller headQueries,
      SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge headCaller before headQueries =
        some (.complete fragment reached saved after) := by
  induction invocation with
  | here observed => exact ⟨_, List.mem_cons_self, _, _, observed⟩
  | completed _ _ _ ih | other _ _ _ _ ih =>
      obtain ⟨edge, member, headCaller, headQueries, observed⟩ := ih
      exact ⟨edge, List.mem_cons_of_mem _ member, headCaller, headQueries, observed⟩

end MicroCFTA.SourcePruningEnumerationHookInvocation
