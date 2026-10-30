import MicroCFTA.SourcePruningEnumerationPathTerminal

/-!
# Paths at raw outer cores and successful returned cores

The statements cover rejected outcomes and missing cache candidates.
Each stated core preserves the same input path predicate.
-/
namespace MicroCFTA
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}

namespace SourcePruningEnumerationTerminal
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] terminalMonadList

/-- Every actual raw outer core preserves the original path predicate. -/
theorem run_outer_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (paths : StatePaths P before) (inputs : BucketPaths P incomingScs) :
    StatePaths P (run checkEmpty r n p h first rest waiting caller before incoming incomingScs queries).2.2.2.1 := by
  generalize observedEq : run checkEmpty r n p h first rest waiting caller before incoming incomingScs queries = observed
  obtain ⟨result, reached, saved, outer, finalWaiting⟩ := observed
  dsimp only
  unfold run at observedEq
  split at observedEq
  next empty =>
    simp only [Prod.mk.injEq] at observedEq
    rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact paths
  next nonempty =>
    split at observedEq
    next recorded winner moved joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest waiting)
          before (recorded, winner, moved) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedPaths := SourcePruningEnumerationTerminalPrefix.run_paths (P := P)
        r first rest waiting before joined recorded winner moved paths prefixSuccess
      rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observedEq
      have foldPaths := SourcePruningEnumerationFold.run_paths (P := P) checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedPaths foldObserved
      cases foldResult with
      | error fault =>
          simp only [Prod.mk.injEq] at observedEq
          rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
          exact foldPaths
      | ok possible =>
          cases possible with
          | none =>
              simp only [Prod.mk.injEq] at observedEq
              rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
              exact foldPaths
          | some raw =>
              cases raw with
              | nil =>
                  simp only [Prod.mk.injEq] at observedEq
                  rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
                  exact foldPaths
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [Prod.mk.injEq] at observedEq
                      rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
                      exact foldPaths
                  | ok payload =>
                      rcases payload with ⟨⟨⟩, folded⟩
                      cases tail with
                      | cons next later =>
                          simp only [Prod.mk.injEq] at observedEq
                          rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
                          exact foldPaths
                      | nil =>
                          have foldedSame := SourcePruningEnumerationFold.singleton_core checkEmpty n p h recorded
                            caller joined winner queries folded foldCaller foldQueries foldOuter foldObserved
                          have foldedPaths : StatePaths P folded := by
                            simpa only [foldedSame] using foldPaths
                          have incomingPaths := (SourcePruningEnumerationIncomingNode.run_paths (P := P)
                            checkEmpty r n p h foldCaller folded winner incoming incomingScs foldQueries foldedPaths inputs).1
                          rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                              foldCaller folded winner incoming incomingScs foldQueries with
                            ⟨incomingResult, afterCaller, savedQueries, read⟩
                          dsimp only at observedEq
                          rw [incomingObserved] at observedEq incomingPaths
                          dsimp only at incomingPaths
                          cases incomingResult with
                          | error fault =>
                              simp only [Prod.mk.injEq] at observedEq
                              rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
                              exact incomingPaths
                          | ok possible =>
                              cases possible <;>
                                simp only [Prod.mk.injEq] at observedEq <;>
                                rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
                                exact incomingPaths
    next other =>
      simp only [Prod.mk.injEq] at observedEq
      rcases observedEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact paths

/-- A raw singleton result preserves paths without a cache-candidate premise. -/
theorem returned_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (outer after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (paths : StatePaths P before) (inputs : BucketPaths P incomingScs)
    (observed : run checkEmpty r n p h first rest waiting caller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, outer, moved)) : StatePaths P after := by
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
      have joinedPaths := SourcePruningEnumerationTerminalPrefix.run_paths (P := P) r first rest waiting
        before joined recorded winner transfer paths prefixSuccess
      rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observed
      have foldPaths := SourcePruningEnumerationFold.run_paths (P := P) checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedPaths foldObserved
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
            have foldedPaths : StatePaths P folded := by simpa only [foldedSame] using foldPaths
            have incomingPaths := SourcePruningEnumerationIncomingNode.run_paths (P := P) checkEmpty r n p h
              foldCaller folded winner incoming incomingScs foldQueries foldedPaths inputs
            rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                foldCaller folded winner incoming incomingScs foldQueries with
              ⟨incomingResult, reached, saved, read⟩
            rw [incomingObserved] at observed incomingPaths
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
                exact incomingPaths.2 after (by rw [single])
          next other => cases observed
    next other => cases observed

end SourcePruningEnumerationTerminal

namespace SourcePruningEnumerationCachedTerminalAdapter
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual raw outer core preserves the original path predicate. -/
theorem run_outer_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (paths : StatePaths P before.core) (inputs : BucketPaths P incomingScs) :
    StatePaths P (run checkEmpty r n p h k first rest caller before incoming incomingScs queries).1.2.2.2.1 := by
  rw [erase checkEmpty r n p h k first rest caller before incoming incomingScs queries]
  exact SourcePruningEnumerationTerminal.run_outer_paths (P := P)
    checkEmpty r n p h first rest before.waiting caller before.core incoming incomingScs queries paths inputs

end SourcePruningEnumerationCachedTerminalAdapter

namespace SourcePruningEnumerationShallowChild
open Fragments EnumerationSemantics EnumerationProgress

private theorem prepared_paths {EnumGuard NativeGuard : Type} {P : EqualityTrie.Path → Prop}
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) (fragment : Fragments.Fragment Symbol)
    (paths : StatePaths P before) (inputs : BucketPaths P scs)
    (prepared : prepareChild scs value = some action)
    (success : Success action before fragment after) : StatePaths P after := by
  cases value with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      exact (reject_unsuccessful before after fragment success).elim
  | reference name =>
      simp only [prepareChild, reduceCtorEq] at prepared
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have writtenPaths := SourcePruningEnumerationPathStorage.setValue_paths (P := P) before.counter
          (.unenumerated (some (entry.identity + 1)) scs)
          (allocated (some (entry.identity + 1)) before) written
          (paths.allocated (some (entry.identity + 1))) inputs writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        exact writtenPaths
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
        exact paths.allocated (some (entry.identity + 1))


end SourcePruningEnumerationShallowChild

namespace SourcePruningEnumerationChildDispatch
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual raw outer core preserves the original path predicate. -/
theorem run_outer_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs) :
    StatePaths P (run checkEmpty r n p h k scs incoming caller before queries).1.2.2.2.1 := by
  rw [erase checkEmpty r n p h k scs incoming caller before queries]
  by_cases empty : incoming = .empty
  · simpa only [observe, empty, ↓reduceIte] using paths
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
          | none => simpa only [observe, ite_eq_right empty, partitioned, prepared] using paths
          | some action => simpa only [observe, ite_eq_right empty, partitioned, prepared] using paths
      | cons first rest =>
          have descendantsSame : scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie) = descendants := by
            simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
          have descendantPaths : BucketPaths P descendants := by
            intro sc member path represented
            have originalMember : sc ∈ scs := by
              have filteredMember : sc ∈ scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie) := by
                simpa only [descendantsSame] using member
              exact (List.mem_filter.mp filteredMember).1
            exact inputs sc originalMember path represented
          simpa only [observe, ite_eq_right empty, partitioned] using
            SourcePruningEnumerationTerminal.run_outer_paths (P := P) checkEmpty r n p h
              first rest before.waiting caller before.core incoming descendants queries paths descendantPaths

/-- A raw singleton result preserves paths without a cache-candidate premise. -/
theorem returned_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller reachedCaller : Caller width) (before : Cached) (queries savedQueries : Queries)
    (fragment : Fragment) (returned outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs)
    (observed : (run checkEmpty r n p h k scs incoming caller before queries).1 =
      (.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting)) :
    StatePaths P returned := by
  have plain := (erase checkEmpty r n p h k scs incoming caller before queries).symm.trans observed
  by_cases empty : incoming = .empty
  · simp only [observe, empty, ↓reduceIte] at plain
    cases plain
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
          | none =>
              simp only [observe, ite_eq_right empty, partitioned, prepared] at plain
              cases plain
          | some action =>
              simp only [observe, ite_eq_right empty, partitioned, prepared, Prod.mk.injEq] at plain
              rcases plain with ⟨rawSame, rfl, rfl, rfl, rfl⟩
              have rawExact := Option.some.inj (Except.ok.inj rawSame)
              apply SourcePruningEnumerationShallowChild.prepared_paths scs incoming before.core returned
                action fragment paths inputs prepared
              rw [Success, rawExact]
              exact List.mem_singleton_self _
      | cons first rest =>
          have descendantsSame : scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie) = descendants := by
            simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
          have descendantPaths : BucketPaths P descendants := by
            intro sc member path represented
            have originalMember : sc ∈ scs := by
              have filteredMember : sc ∈ scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie) := by
                simpa only [descendantsSame] using member
              exact (List.mem_filter.mp filteredMember).1
            exact inputs sc originalMember path represented
          apply SourcePruningEnumerationTerminal.returned_paths (P := P) checkEmpty r n p h
            first rest before.waiting caller before.core incoming descendants queries fragment
            reachedCaller savedQueries outer returned waiting paths descendantPaths
          simpa only [observe, ite_eq_right empty, partitioned] using plain

end SourcePruningEnumerationChildDispatch
end MicroCFTA
