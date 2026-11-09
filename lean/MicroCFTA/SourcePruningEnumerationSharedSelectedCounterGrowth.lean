import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedTraversalScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedSelectedEdgeScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedCapturedEdgeScalarBounds

/-!
# Counter growth at actual shared selected stages

The attached cache is the cache of the actual observation.
Rejected and stopped observations retain their own cache.
The proofs do not require a native caller context or future completion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedCounterGrowth
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every attached receipt cache retains the original allocated domain. -/
def ReceiptGrows (counter : Nat) : Receipt width → Prop
  | .unhandled => True
  | .complete _ _ _ after | .rejected _ _ after | .finalizeStopped _ _ _ after =>
      counter ≤ after.core.counter
  | .stopped _ _ candidate => ∀ after, candidate = some after → counter ≤ after.core.counter

/-- Actual child allocation and terminal assimilation do not decrease the counter. -/
theorem child
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) (after : Cached)
    (observed : (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    before.core.counter ≤ after.core.counter := by
  by_cases empty : incoming = .empty
  · simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
      ite_eq_left empty, Option.some.injEq] at observed
    subst after
    exact Nat.le_refl _
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
          ite_eq_right empty, partitioned] at observed
        cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild
            caller.checked.native.machine.heap k scs incoming before with
        | none => simp only [prepared] at observed; cases observed
        | some rows =>
          cases rows with
          | nil =>
            simp only [prepared, Option.some.injEq] at observed
            subst after
            exact Nat.le_refl _
          | cons row rest =>
            rcases row with ⟨fragment, returned⟩
            cases rest with
            | cons second remaining => simp only [prepared] at observed; cases observed
            | nil =>
              simp only [prepared, Option.some.injEq] at observed
              subst after
              have bounds := SourcePruningEnumerationCachedPrepare.singleton_counter_mass_bound
                caller.checked.native.machine.heap k scs incoming before returned fragment prepared
              rw [bounds.1]
              exact Nat.le_succ _
      | cons first rest =>
        have bounds := SourcePruningEnumerationSharedCachedTerminal.observed_cache_bounds
          checkEmpty r n p h k first rest caller before incoming descendants queries after
          (by simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
            ite_eq_right empty, partitioned] using observed)
        rw [bounds.1]
        exact Nat.le_refl _

/-- Every actual complete or attached stopped traversal cache retains the allocated domain. -/
theorem traversal
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries) :
    match SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run
      checkEmpty r n p h k inputs caller before queries with
    | .complete _ _ _ after => before.core.counter ≤ after.core.counter
    | .stopped _ _ candidate =>
        ∀ after, candidate = some after → before.core.counter ≤ after.core.counter := by
  induction inputs generalizing caller before queries with
  | nil => exact Nat.le_refl _
  | cons input rest ih =>
    rcases input with ⟨value, bucket⟩
    cases headEq : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
        checkEmpty r n p h k bucket value caller before queries with
    | mk observation candidate =>
      have stoppedHere : ∀ after, candidate = some after → before.core.counter ≤ after.core.counter := by
        intro after recovered
        exact child checkEmpty r n p h k bucket value caller before queries after
          (by rw [headEq]; exact recovered)
      rcases observation with ⟨outcome, middleCaller, middleQueries, outer, waiting⟩
      cases outcome with
      | error fault =>
        simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq] using stoppedHere
      | ok returned =>
        cases returned with
        | none =>
          simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq] using stoppedHere
        | some raw =>
          cases raw with
          | nil =>
            simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq] using stoppedHere
          | cons row rows =>
            cases row with
            | error fault =>
              simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq] using stoppedHere
            | ok payload =>
              rcases payload with ⟨fragment, returned⟩
              cases rows with
              | cons second remaining =>
                simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq] using stoppedHere
              | nil =>
                cases candidate with
                | none =>
                  simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq] using stoppedHere
                | some middle =>
                  have headGrowth := child checkEmpty r n p h k bucket value caller before queries middle
                    (by rw [headEq])
                  have tailGrowth := ih middleCaller middle middleQueries
                  cases tailEq : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run
                      checkEmpty r n p h k rest middleCaller middle middleQueries with
                  | complete fragments finalCaller finalQueries final =>
                    simp only [tailEq] at tailGrowth
                    simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq, tailEq] using
                      Nat.le_trans headGrowth tailGrowth
                  | stopped fragments finalObservation finalCandidate =>
                    simp only [tailEq] at tailGrowth
                    simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headEq, tailEq]
                    intro after recovered
                    exact Nat.le_trans headGrowth (tailGrowth after recovered)

/-- Own-class allocation and ordered child execution retain the allocated domain. -/
theorem selected
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    ReceiptGrows before.core.counter
      (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.run
        checkEmpty r n p h k scs edge caller before queries) := by
  unfold SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.run
  cases prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before with
  | none => trivial
  | some rows =>
    cases rows with
    | nil => exact Nat.le_refl _
    | cons row rest =>
      rcases row with ⟨⟨symbol, staged, savedResidual⟩, middle⟩
      cases rest with
      | cons second remaining => trivial
      | nil =>
        have own := SourcePruningEnumerationCachedOwn.prepare_scalars
          caller.checked.native.machine.heap scs edge before middle tries residual
          (symbol, staged, savedResidual) projected prepared
        have ownGrowth : before.core.counter ≤ middle.core.counter := by
          rw [own.2.2.1]
          exact Nat.le_add_right _ _
        have tail := traversal checkEmpty r n p h k
          (staged.map fun input => (input.1, input.2.1)) caller middle queries
        dsimp only
        cases traversed : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run
            checkEmpty r n p h k (staged.map fun input => (input.1, input.2.1)) caller middle queries with
        | complete fragments afterCaller saved after =>
          simp only [traversed] at tail
          change before.core.counter ≤ after.core.counter
          exact Nat.le_trans ownGrowth tail
        | stopped fragments observation candidate =>
          simp only [traversed] at tail
          intro after recovered
          exact Nat.le_trans ownGrowth (tail after recovered)

/-- Captured finalization retains the counter of the actual selected cache. -/
theorem captured
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    match SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run
      checkEmpty r n p h k target scs edge caller before queries with
    | none => True
    | some receipt => ReceiptGrows before.core.counter receipt := by
  have growth := selected checkEmpty r n p h k scs edge caller before queries tries residual projected
  unfold SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run
  cases chosen : SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.run
      checkEmpty r n p h k scs edge caller before queries with
  | unhandled => trivial
  | rejected reached saved after | finalizeStopped _ reached saved after =>
    simpa only [chosen] using growth
  | stopped fragments observation candidate =>
    simpa only [chosen] using growth
  | complete fragment reached saved middle =>
    simp only [chosen] at growth
    dsimp only
    cases finished : SourcePruningEnumerationFinalize.run
        reached.checked.native.machine.heap k target fragment middle with
    | none => exact growth
    | some after =>
      have same := (SourcePruningEnumerationFinalize.run_scalars
        reached.checked.native.machine.heap k target fragment middle after finished).1
      change before.core.counter ≤ after.core.counter
      rw [same]
      exact growth

end MicroCFTA.SourcePruningEnumerationSharedSelectedCounterGrowth
