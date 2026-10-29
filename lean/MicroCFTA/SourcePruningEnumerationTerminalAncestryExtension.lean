import MicroCFTA.SourcePruningEnumerationTerminalPrefixAncestryExtension
import MicroCFTA.SourcePruningEnumerationFoldAncestryExtension
import MicroCFTA.SourcePruningEnumerationFoldCacheBounds
import MicroCFTA.SourcePruningEnumerationIncomingAncestryExtension
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter

/-!
# Recursion ancestry at actual terminal cache candidates

The actual prefix, ordered fold and incoming write extend all old slot keys.
Their exact expansion equalities compose at the same returned cache.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
open EnumerationState EnumerationCorrectness SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- Every actual attached terminal cache extends all slots and retains exact expansion ancestry. -/
theorem candidate_ancestry_extension
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (after : Cached)
    (candidate : (run checkEmpty r n p h k first rest caller before incoming incomingScs queries).2 = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  unfold run at candidate
  split at candidate
  next empty =>
    have same : before = after := Option.some.inj candidate
    subst after
    exact ⟨Extends.refl before.core, rfl⟩
  next nonempty =>
    split at candidate
    next recorded winner moved joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting)
          before.core (recorded, winner, moved) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedFields := SourcePruningEnumerationTerminalPrefix.run_ancestry_extension r first rest before.waiting
        before.core joined recorded winner moved prefixSuccess
      rcases foldObserved : SourcePruningEnumerationCachedFold.run checkEmpty n p h recorded
          caller ⟨joined, before.expandable, moved⟩ winner queries with
        ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
      rw [foldObserved] at candidate
      have foldExact := (SourcePruningEnumerationCachedFold.erase checkEmpty n p h recorded
        caller ⟨joined, before.expandable, moved⟩ winner queries).symm.trans (congrArg Prod.fst foldObserved)
      have foldFields := SourcePruningEnumerationFold.run_ancestry_extension checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter foldExact
      cases foldResult with
      | error fault => cases candidate
      | ok possible =>
        cases possible with
        | none => cases candidate
        | some raw =>
          cases raw with
          | nil =>
            have cacheFields := SourcePruningEnumerationCachedFold.candidate_ancestry_extension checkEmpty n p h recorded
              caller ⟨joined, before.expandable, moved⟩ winner queries after (by
                rw [foldObserved]
                exact candidate)
            exact ⟨joinedFields.1.trans cacheFields.1, cacheFields.2.trans joinedFields.2⟩
          | cons row tail =>
            cases row with
            | error fault => cases candidate
            | ok payload =>
              rcases payload with ⟨⟨⟩, folded⟩
              cases tail with
              | cons next later => cases candidate
              | nil =>
                have foldedSame := SourcePruningEnumerationFold.singleton_core checkEmpty n p h recorded
                  caller joined winner queries folded foldCaller foldQueries foldOuter foldExact
                have foldedFields : Extends before.core folded ∧
                    folded.expansionAncestry = before.core.expansionAncestry := by
                  simpa only [foldedSame] using And.intro (joinedFields.1.trans foldFields.1)
                    (foldFields.2.trans joinedFields.2)
                cases foldCache with
                | none =>
                  dsimp only at candidate
                  rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                      foldCaller folded winner incoming incomingScs foldQueries with
                    ⟨incomingResult, reached, saved, read⟩
                  rw [incomingObserved] at candidate
                  cases incomingResult with
                  | error fault => cases candidate
                  | ok possible => cases possible <;> cases candidate
                | some recovered =>
                  dsimp only at candidate
                  rcases incomingObserved : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
                      foldCaller (EnumerationExpandableIndex.frame folded recovered)
                      winner incoming incomingScs foldQueries with
                    ⟨⟨incomingResult, reached, saved, read⟩, incomingCache⟩
                  rw [incomingObserved] at candidate
                  cases incomingResult with
                  | error fault => cases candidate
                  | ok possible =>
                    cases possible with
                    | none => cases candidate
                    | some incomingRaw =>
                      have incomingFields := SourcePruningEnumerationIncomingCacheAdapter.observed_cache_ancestry_extension
                        checkEmpty r n p h k foldCaller (EnumerationExpandableIndex.frame folded recovered)
                        winner incoming incomingScs foldQueries after (by
                          rw [incomingObserved]
                          exact candidate)
                      exact ⟨foldedFields.1.trans incomingFields.1, incomingFields.2.trans foldedFields.2⟩
    next other => cases candidate

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
