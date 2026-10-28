import MicroCFTA.SourcePruningEnumerationTerminalPrefixCarriers
import MicroCFTA.SourcePruningEnumerationFoldCarriers
import MicroCFTA.SourcePruningEnumerationFoldCacheBounds
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
import MicroCFTA.SourcePruningEnumerationIncomingCarriers

/-!
# Graph provenance in actual terminal rows and attached caches

The prefix joins the actual recorded classes.
The fold transfers each eliminated source carrier to that class.
The incoming write supplies the actual returned hole.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics EnumerationCarriers EnumerationGraphReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] terminalMonadList

/-- An actual terminal row preserves old carriers and supplies every returned hole. -/
theorem successful_carriers
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (outer after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (observed : run checkEmpty r n p h first rest waiting caller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, outer, moved)) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧
      ReferencesCarry after ∧ FragmentCarries after fragment := by
  unfold run at observed
  split at observed
  next empty => cases observed
  next nonempty =>
    split at observed
    next recorded winner transfer joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest waiting)
          before (recorded, winner, transfer) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedFacts := SourcePruningEnumerationTerminalPrefix.run_carriers r first rest waiting
        before joined recorded winner transfer total references prefixSuccess
      rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observed
      have foldFacts := SourcePruningEnumerationFold.run_carriers checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedFacts.1 joinedFacts.2.2.2
        joinedFacts.2.2.1 foldObserved
      cases foldResult with
      | error fault => cases observed
      | ok possible =>
        cases possible with
        | none => cases observed
        | some raw =>
          dsimp only at observed
          split at observed
          next empty => cases observed
          next folded =>
            have foldedSame := SourcePruningEnumerationFold.singleton_core checkEmpty n p h recorded
              caller joined winner queries folded foldCaller foldQueries foldOuter foldObserved
            have foldedTotal : UnionFind.Total folded.representatives := by simpa only [foldedSame] using foldFacts.1
            have foldedReferences : ReferencesCarry folded := by simpa only [foldedSame] using foldFacts.2.2
            have foldedPreserves : PreservesCarriers joined folded := by simpa only [foldedSame] using foldFacts.2.1
            have incomingFacts := SourcePruningEnumerationIncomingNode.run_carriers checkEmpty r n p h
              foldCaller folded winner incoming incomingScs foldQueries foldedTotal foldedReferences
            rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                foldCaller folded winner incoming incomingScs foldQueries with
              ⟨incomingResult, reached, saved, read⟩
            rw [incomingObserved] at observed incomingFacts
            cases incomingResult with
            | error fault => cases observed
            | ok result =>
              cases result with
              | none => cases observed
              | some incomingRaw =>
                have rowsSame := congrArg Prod.fst observed
                dsimp only at rowsSame
                have mapped := Option.some.inj (Except.ok.inj rowsSame)
                have single : incomingRaw = [.ok ((), after)] := by
                  cases incomingRaw with
                  | nil => cases mapped
                  | cons row rest =>
                    cases row with
                    | error error => cases mapped
                    | ok value =>
                      rcases value with ⟨⟨⟩, returned⟩
                      have fields := List.cons.inj mapped
                      have coreSame : returned = after := (Prod.mk.inj (Except.ok.inj fields.1)).2
                      have restEmpty : rest = [] := List.map_eq_nil_iff.mp fields.2
                      simp only [coreSame, restEmpty]
                have fragmentSame : fragment = .hole winner := by
                  rw [single] at mapped
                  exact (Prod.mk.inj (Except.ok.inj (List.cons.inj mapped).1)).1.symm
                obtain ⟨afterTotal, preserved, afterReferences, carried⟩ := incomingFacts.2 after (by rw [single])
                refine ⟨afterTotal, joinedFacts.2.1.trans (foldedPreserves.trans preserved), afterReferences, ?_⟩
                rw [fragmentSame]
                exact fragmentCarries_hole after winner carried
          next other => cases observed
    next other => cases observed

end MicroCFTA.SourcePruningEnumerationTerminal

namespace MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
open EnumerationState EnumerationCorrectness EnumerationCarriers EnumerationGraphReferences InternedConstructorTemplates
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

/-- Every attached terminal cache retains the carriers of its actual prefix. -/
theorem candidate_carriers
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (total : UnionFind.Total before.core.representatives)
    (references : ReferencesCarry before.core) (after : Cached)
    (candidate : (run checkEmpty r n p h k first rest caller before incoming incomingScs queries).2 = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  unfold run at candidate
  split at candidate
  next empty =>
    have same : before = after := Option.some.inj candidate
    subst after
    exact ⟨total, .refl _, references⟩
  next nonempty =>
    split at candidate
    next recorded winner moved joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting)
          before.core (recorded, winner, moved) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedFacts := SourcePruningEnumerationTerminalPrefix.run_carriers r first rest before.waiting
        before.core joined recorded winner moved total references prefixSuccess
      rcases foldObserved : SourcePruningEnumerationCachedFold.run checkEmpty n p h recorded
          caller ⟨joined, before.expandable, moved⟩ winner queries with
        ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
      rw [foldObserved] at candidate
      have foldExact := (SourcePruningEnumerationCachedFold.erase checkEmpty n p h recorded
        caller ⟨joined, before.expandable, moved⟩ winner queries).symm.trans (congrArg Prod.fst foldObserved)
      have foldFacts := SourcePruningEnumerationFold.run_carriers checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedFacts.1 joinedFacts.2.2.2
        joinedFacts.2.2.1 foldExact
      cases foldResult with
      | error fault => cases candidate
      | ok possible =>
        cases possible with
        | none => cases candidate
        | some raw =>
          cases raw with
          | nil =>
            have cached := SourcePruningEnumerationCachedFold.candidate_carriers checkEmpty n p h recorded
              caller ⟨joined, before.expandable, moved⟩ winner queries joinedFacts.1 joinedFacts.2.2.2
              joinedFacts.2.2.1 after (by rw [foldObserved]; exact candidate)
            exact ⟨cached.1, joinedFacts.2.1.trans cached.2.1, cached.2.2⟩
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
                have foldedTotal : UnionFind.Total folded.representatives := by simpa only [foldedSame] using foldFacts.1
                have foldedReferences : ReferencesCarry folded := by simpa only [foldedSame] using foldFacts.2.2
                have foldedPreserves : PreservesCarriers joined folded := by simpa only [foldedSame] using foldFacts.2.1
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
                      have incomingFacts := SourcePruningEnumerationIncomingCacheAdapter.observed_cache_carriers checkEmpty r n p h k
                        foldCaller (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs
                        foldQueries foldedTotal foldedReferences after (by rw [incomingObserved]; exact candidate)
                      exact ⟨incomingFacts.1, joinedFacts.2.1.trans (foldedPreserves.trans incomingFacts.2.1),
                        incomingFacts.2.2.1⟩
    next other => cases candidate

end MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
