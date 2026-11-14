import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
import MicroCFTA.SourcePruningEnumerationSharedCachedFoldStability
import MicroCFTA.SourcePruningEnumerationSharedIncomingNodeStability
import MicroCFTA.SourcePruningEnumerationTerminalPrefixStability
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapterStability

/-!
# Exact successful actual shared terminal observations

Empty rejection and successful singleton rows retain every reached endpoint.
The pure prefix and index adapter keep their existing operations.
The native calls use the actual shared incoming and fold replay laws.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Fragments.Fragment Symbol × Core))
local notation "IncomingRaw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}

private theorem incoming_rows_clean (winner : Nat) {incomingRaw : IncomingRaw} {raw : Raw}
    (mapped : incomingRaw.map (fun row => match row with
      | .error error => .error error
      | .ok result => .ok (.hole winner, result.2)) = raw)
    (clean : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)]) :
    incomingRaw = [] ∨ ∃ returned, incomingRaw = [.ok ((), returned)] := by
  rcases clean with empty | ⟨fragment, returned, single⟩
  · exact .inl (List.map_eq_nil_iff.mp (mapped.trans empty))
  · have singleMap := mapped.trans single
    cases incomingRaw with
    | nil => cases singleMap
    | cons row rest =>
      cases row with
      | error fault => cases singleMap
      | ok result =>
        rcases result with ⟨⟨⟩, actual⟩
        have restEmpty : rest = [] := List.map_eq_nil_iff.mp (List.cons.inj singleMap).2
        exact .inr ⟨actual, by simp only [restEmpty]⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] sharedTerminalMonadList

/-- The actual shared incoming row and Some cache retain every endpoint at larger bounds. -/
theorem incomingCacheAdapter_some_stable
    {checkEmpty : Bool} {r n p h k R N P H K : Nat}
    {caller reached : Caller width} {before after : Cached} {read : Core}
    {target : Nat} {incoming : Node} {incomingScs : List Suspended} {queries saved : Queries} {raw : IncomingRaw}
    (observed : incomingCacheAdapter checkEmpty r n p h k caller before target incoming incomingScs queries =
      ((.ok (some raw), reached, saved, read), some after))
    (successful : raw = [] ∨ ∃ returned : Core, raw = [.ok ((), returned)])
    (enoughR : r ≤ R) (enoughN : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughK : k ≤ K) :
    incomingCacheAdapter checkEmpty R N P H K caller before target incoming incomingScs queries =
      ((.ok (some raw), reached, saved, read), some after) := by
  have original : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before.core
      target incoming incomingScs queries = (.ok (some raw), reached, saved, read) := by
    simpa only [incomingCacheAdapter] using congrArg Prod.fst observed
  have larger := SourcePruningEnumerationSharedIncomingNode.run_ok_stable
    original successful enoughR enoughN enoughP enoughH
  have adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt reached.checked.native.machine.heap k target incomingScs before read raw = some after := by
    simpa only [incomingCacheAdapter, original] using congrArg Prod.snd observed
  simp only [incomingCacheAdapter, larger, SourcePruningEnumerationIncomingCacheAdapter.adapt_some_stable adapted enoughK]

/-- A clean actual raw terminal result retains every returned field at larger bounds. -/
theorem raw_ok_stable
    {checkEmpty : Bool} {r R n N p P h H : Nat}
    {first : Suspended} {rest : List Suspended} {waiting : EnumerationWaitingIndex.Waiting}
    {beforeCaller afterCaller : Caller width} {before outer : Core}
    {incoming : Node} {incomingScs : List Suspended} {queries savedQueries : Queries}
    {raw : Raw} {moved : EnumerationWaitingIndex.Waiting}
    (observed : SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty r n p h first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some raw), afterCaller, savedQueries, outer, moved))
    (successful : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)])
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty R N P H first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some raw), afterCaller, savedQueries, outer, moved) := by
  unfold SourcePruningEnumerationSharedCachedTerminal.raw at observed ⊢
  by_cases empty : incoming = .empty
  · simp only [ite_eq_left empty] at observed ⊢
    exact observed
  · simp only [ite_eq_right empty] at observed ⊢
    cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) with
    | nil =>
      simp only [prefixObserved] at observed
      cases observed
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error fault =>
        simp only [prefixObserved] at observed
        cases observed
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, transfer⟩, joined⟩
        cases prefixTail with
        | cons second remaining =>
          simp only [prefixObserved] at observed
          cases observed
        | nil =>
          have prefixLater := SourcePruningEnumerationTerminalPrefix.run_singleton_stable
            prefixObserved enoughRepresentative
          simp only [prefixObserved] at observed
          rw [prefixLater]
          dsimp only
          rcases foldObserved : rawFold checkEmpty n p h recorded
              beforeCaller joined winner queries with
            ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
          rw [foldObserved] at observed
          cases foldResult with
          | error fault => cases observed
          | ok possible =>
            have foldLater := rawFold_ok_stable
              foldObserved enoughNative enoughP enoughH
            rw [foldLater]
            cases possible with
            | none => cases observed
            | some foldRaw =>
              cases foldRaw with
              | nil => exact observed
              | cons row tail =>
                cases row with
                | error fault => cases observed
                | ok result =>
                  rcases result with ⟨⟨⟩, folded⟩
                  cases tail with
                  | cons second remaining => cases observed
                  | nil =>
                    dsimp only at observed ⊢
                    rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                        foldCaller folded winner incoming incomingScs foldQueries with
                      ⟨incomingResult, reached, saved, read⟩
                    rw [incomingObserved] at observed
                    cases incomingResult with
                    | error fault => cases observed
                    | ok possible =>
                      cases possible with
                      | none => cases observed
                      | some incomingRaw =>
                        have mapped := Option.some.inj (Except.ok.inj (congrArg Prod.fst observed))
                        have incomingSuccessful := incoming_rows_clean winner mapped successful
                        have incomingLater := SourcePruningEnumerationSharedIncomingNode.run_ok_stable
                          incomingObserved incomingSuccessful enoughRepresentative enoughNative enoughP enoughH
                        rw [incomingLater]
                        exact observed


/-- A clean actual shared terminal result retains its full Some cache and every endpoint. -/
theorem run_some_stable
    {checkEmpty : Bool} {r R n N p P h H k K : Nat}
    {first : Suspended} {rest : List Suspended}
    {beforeCaller afterCaller : Caller width} {before after : Cached} {outer : Core}
    {incoming : Node} {incomingScs : List Suspended} {queries savedQueries : Queries}
    {raw : Raw} {moved : EnumerationWaitingIndex.Waiting}
    (observed : run checkEmpty r n p h k first rest beforeCaller before incoming incomingScs queries =
      ((.ok (some raw), afterCaller, savedQueries, outer, moved), some after))
    (successful : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)])
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    run checkEmpty R N P H K first rest beforeCaller before incoming incomingScs queries =
      ((.ok (some raw), afterCaller, savedQueries, outer, moved), some after) := by
  unfold run at observed ⊢
  by_cases empty : incoming = .empty
  · simp only [ite_eq_left empty] at observed ⊢
    exact observed
  · simp only [ite_eq_right empty] at observed ⊢
    cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        r first rest before.waiting before.core) with
    | nil =>
      simp only [prefixObserved] at observed
      cases observed
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error fault =>
        simp only [prefixObserved] at observed
        cases observed
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, transfer⟩, joined⟩
        cases prefixTail with
        | cons second remaining =>
          simp only [prefixObserved] at observed
          cases observed
        | nil =>
          have prefixLater := SourcePruningEnumerationTerminalPrefix.run_singleton_stable
            prefixObserved enoughRepresentative
          simp only [prefixObserved] at observed
          rw [prefixLater]
          dsimp only
          rcases foldObserved : fold checkEmpty n p h recorded
              beforeCaller ⟨joined, before.expandable, transfer⟩ winner queries with
            ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
          rw [foldObserved] at observed
          cases foldResult with
          | error fault => cases observed
          | ok possible =>
            have foldLater := fold_ok_stable
              foldObserved enoughNative enoughP enoughH
            rw [foldLater]
            cases possible with
            | none => cases observed
            | some foldRaw =>
              cases foldRaw with
              | nil => exact observed
              | cons row tail =>
                cases row with
                | error fault => cases observed
                | ok result =>
                  rcases result with ⟨⟨⟩, folded⟩
                  cases tail with
                  | cons second remaining => cases observed
                  | nil =>
                    cases foldCache with
                    | none =>
                      dsimp only at observed
                      rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                          foldCaller folded winner incoming incomingScs foldQueries with
                        ⟨incomingResult, reached, saved, read⟩
                      rw [incomingObserved] at observed
                      cases incomingResult with
                      | error fault => cases observed
                      | ok possible =>
                        cases possible with
                        | none => cases observed
                        | some incomingRaw =>
                          have impossible : (none : Option Cached) = some after := congrArg Prod.snd observed
                          cases impossible
                    | some recovered =>
                      dsimp only at observed ⊢
                      rcases incomingObserved : incomingCacheAdapter
                          checkEmpty r n p h k foldCaller (EnumerationExpandableIndex.frame folded recovered)
                          winner incoming incomingScs foldQueries with
                        ⟨⟨incomingResult, reached, saved, read⟩, incomingCache⟩
                      rw [incomingObserved] at observed
                      cases incomingResult with
                      | error fault => cases observed
                      | ok possible =>
                        cases possible with
                        | none => cases observed
                        | some incomingRaw =>
                          have mapped := Option.some.inj (Except.ok.inj
                            (congrArg (fun result => result.1.1) observed))
                          have incomingSuccessful := incoming_rows_clean winner mapped successful
                          have cacheSame : incomingCache = some after := congrArg Prod.snd observed
                          rw [cacheSame] at incomingObserved observed
                          have incomingLater := incomingCacheAdapter_some_stable
                            incomingObserved incomingSuccessful enoughRepresentative enoughNative enoughP enoughH enoughIndex
                          rw [incomingLater]
                          exact observed

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal


#check MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter_some_stable
#print axioms MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter_some_stable

#check MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.raw_ok_stable
#print axioms MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.raw_ok_stable

#check MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.run_some_stable
#print axioms MicroCFTA.SourcePruningEnumerationSharedCachedTerminal.run_some_stable
