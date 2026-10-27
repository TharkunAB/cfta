import MicroCFTA.SourceFlatPruningRecursive

/-!
# Output properties through actual flat continuations

These structural laws retain outputs from complete and stopped computations.
The sibling law reads the actual hook and caller-threaded suffix.
-/
namespace MicroCFTA.SourceFlatPruningOutputFlow
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "HookResult" => SourceFlatPruningNativeContinuations.HookResult
local notation "FoldResult" => SourceFlatPruningNativeContinuations.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- Read every emitted output, including outputs before a stopped continuation. -/
def hookOutputs : HookResult Output Reason width → List Output
  | .complete outputs _ _ => outputs
  | .stopped outputs _ _ => outputs

/-- Read every emitted output, including outputs before an edge or hook stop. -/
def foldOutputs : FoldResult Output Reason width → List Output
  | .complete _ outputs _ _ => outputs
  | .stopped _ outputs _ => outputs

variable {Typing : Type}

/-- The concrete callback only emits outputs returned by its actual restart continuation. -/
theorem continueWith_outputs
    (property : Output → Prop)
    (callbackFailure : Nat → List (Except Error ((Bool × Metadata Typing) ×
      EnumerationFlatState.State Symbol Constraint)) → Reason)
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → HookResult Output Reason width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (continued : ∀ updated reached saved after, ∀ output ∈ hookOutputs
      (recur updated reached saved after (SourceFlatPruningRestart.decision stop order updated after)), property output) :
    ∀ output ∈ hookOutputs (SourceFlatPruningContinuation.continueWith callbackFailure recur graph templates
      stop order callbackFuel metadata uv fragment caller queries before), property output := by
  unfold SourceFlatPruningContinuation.continueWith
  dsimp only
  split
  · intro output member
    cases member
  · exact continued _ _ _ _
  · intro output member
    cases member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual sibling scan preserves each property supplied by every invoked hook. -/
theorem run_outputs
    (property : Output → Prop)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries)
    (continued : ∀ fragment reached saved after, ∀ output ∈ hookOutputs (hook fragment reached saved after), property output) :
    ∀ output ∈ foldOutputs (SourceFlatPruningNativeContinuations.run hook checkEmpty nativeFuel p h target
      scs before edges caller queries), property output := by
  induction edges generalizing caller queries with
  | nil =>
      intro output member
      cases member
  | cons edge rest ih =>
      cases observed : SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries with
      | none =>
          intro output member
          simp only [SourceFlatPruningNativeContinuations.run, observed, foldOutputs,
            List.not_mem_nil] at member
      | some receipt =>
          cases receipt with
          | unhandled =>
              intro output member
              simp only [SourceFlatPruningNativeContinuations.run, observed,
                SourceFlatPruningNativeBranches.advance, foldOutputs, List.not_mem_nil] at member
          | rejected reached saved after =>
              have suffix := ih reached saved
              cases following : SourceFlatPruningNativeContinuations.run hook checkEmpty nativeFuel p h target
                  scs before rest reached saved <;>
                simpa only [SourceFlatPruningNativeContinuations.run, observed,
                  SourceFlatPruningNativeBranches.advance, following, foldOutputs] using suffix
          | complete fragment reached saved after =>
              have first := continued fragment reached saved after
              cases callback : hook fragment reached saved after with
              | stopped outputs reason endpoint =>
                  simpa only [SourceFlatPruningNativeContinuations.run, observed, callback,
                    foldOutputs, hookOutputs] using first
              | complete outputs middleCaller middleQueries =>
                  have suffix := ih middleCaller middleQueries
                  rw [callback] at first
                  cases following : SourceFlatPruningNativeContinuations.run hook checkEmpty nativeFuel p h target
                      scs before rest middleCaller middleQueries with
                  | complete processed later finalCaller finalQueries =>
                      rw [following] at suffix
                      intro output member
                      have listed : output ∈ outputs ++ later := by
                        simpa only [SourceFlatPruningNativeContinuations.run, observed, callback, following,
                          foldOutputs] using member
                      rcases List.mem_append.mp listed with head | tail
                      · exact first output head
                      · exact suffix output tail
                  | stopped processed later current =>
                      rw [following] at suffix
                      intro output member
                      have listed : output ∈ outputs ++ later := by
                        simpa only [SourceFlatPruningNativeContinuations.run, observed, callback, following,
                          foldOutputs] using member
                      rcases List.mem_append.mp listed with head | tail
                      · exact first output head
                      · exact suffix output tail
          | stopped fragments observation candidate =>
              cases advanced : SourceFlatPruningNativeBranches.advance (.stopped fragments observation candidate) with
              | none =>
                  intro output member
                  simp only [SourceFlatPruningNativeContinuations.run, observed, advanced,
                    foldOutputs, List.not_mem_nil] at member
              | some endpoint =>
                  obtain ⟨reached, saved⟩ := endpoint
                  have suffix := ih reached saved
                  cases following : SourceFlatPruningNativeContinuations.run hook checkEmpty nativeFuel p h target
                      scs before rest reached saved <;>
                    simpa only [SourceFlatPruningNativeContinuations.run, observed, advanced,
                      following, foldOutputs] using suffix

/-- Any present actual ordinary fold preserves the hook's output property. -/
theorem ordinary_outputs
    (property : Output → Prop)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (continued : ∀ fragment reached saved after, ∀ output ∈ hookOutputs (hook fragment reached saved after), property output)
    (result : FoldResult Output Reason width)
    (observed : (SourceFlatPruningNativeOrdinaryContinuations.run hook checkEmpty nativeFuel p h uv
      edgesOf caller before queries).2 = some result) :
    ∀ output ∈ foldOutputs result, property output := by
  unfold SourceFlatPruningNativeOrdinaryContinuations.run at observed
  dsimp only at observed
  split at observed
  · split at observed
    · cases observed
    · have same := Option.some.inj observed
      subst result
      exact run_outputs property hook checkEmpty nativeFuel p h _ _ _ _ caller queries continued
  · cases observed

end MicroCFTA.SourceFlatPruningOutputFlow
