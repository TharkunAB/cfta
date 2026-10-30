import MicroCFTA.SourcePruningEnumerationPathTransport
import MicroCFTA.SourcePruningEnumerationPathStorage
import MicroCFTA.SourcePruningEnumerationPathFold
import MicroCFTA.SourcePruningEnumerationPathIncoming
import MicroCFTA.SourcePruningEnumerationChildProper

/-!
# Paths at actual terminal and child candidates

Every actual attached cache retains the stored path predicate.
The incoming raw-empty case also retains its explicit bucket write.
-/
namespace MicroCFTA
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationProgress
open InternedConstructorTemplates
open SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

namespace SourcePruningEnumerationIncomingCacheAdapter

/-- The literal incoming adapter preserves paths, including its raw-empty write. -/
theorem adapt_paths {P : EqualityTrie.Path → Prop}
    {heap : InternedConstructorTemplates.State Symbol Constraint} {indexFuel target : Nat}
    {incomingScs : List Suspended} {before after : Cached} {read : Core} {raw : Raw}
    (readPaths : StatePaths P read) (inputs : BucketPaths P incomingScs)
    (rows : ∀ returned, raw = [.ok ((), returned)] → StatePaths P returned)
    (adapted : adapt heap indexFuel target incomingScs before read raw = some after) :
    StatePaths P after.core := by
  cases raw with
  | nil =>
      simp only [adapt] at adapted
      split at adapted
      · rename_i oldNode oldScs stored
        simp only [Option.map_eq_some_iff] at adapted
        obtain ⟨written, _written, same⟩ := adapted
        subst after
        have oldPaths : BucketPaths P oldScs :=
          readPaths (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)
        intro value member
        change value ∈ read.values.set target
          (.unenumerated (some 0) (incomingScs ++ oldScs)) at member
        rcases List.mem_or_eq_of_mem_set member with retained | replacement
        · exact readPaths value retained
        · simpa only [replacement, references] using BucketPaths.append inputs oldPaths
      · cases adapted
  | cons row rest =>
      cases row with
      | error fault => simp only [adapt] at adapted; cases adapted
      | ok payload =>
          obtain ⟨⟨⟩, returned⟩ := payload
          cases rest with
          | nil =>
              have coreSame := adapt_singleton_core heap indexFuel target incomingScs
                before after read returned adapted
              simpa only [coreSame] using rows returned rfl
          | cons next later => simp only [adapt] at adapted; cases adapted

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual retained candidate preserves the input path predicate. -/
theorem observed_cache_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (paths : StatePaths P before.core) (inputs : BucketPaths P incomingScs)
    (after : Cached)
    (candidate : (run checkEmpty r n p h k caller before target incoming incomingScs queries).2 = some after) :
    StatePaths P after.core := by
  have fields := SourcePruningEnumerationIncomingNode.run_paths (P := P)
    checkEmpty r n p h caller before.core target incoming incomingScs queries paths inputs
  unfold run at candidate
  generalize original : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming incomingScs queries = observed at fields candidate
  obtain ⟨result, reached, saved, read⟩ := observed
  dsimp only at fields candidate
  cases result with
  | error fault => cases candidate
  | ok payload =>
      cases payload with
      | none => cases candidate
      | some raw =>
          apply adapt_paths fields.1 inputs ?_ candidate
          intro returned rawSame
          exact fields.2 returned (by rw [rawSame])

end SourcePruningEnumerationIncomingCacheAdapter

namespace SourcePruningEnumerationCachedTerminalAdapter
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- Every attached terminal cache preserves paths on successful and rejected branches. -/
theorem candidate_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (paths : StatePaths P before.core)
    (inputs : BucketPaths P incomingScs) (after : Cached)
    (candidate : (run checkEmpty r n p h k first rest caller before incoming incomingScs queries).2 = some after) :
    StatePaths P after.core := by
  unfold run at candidate
  split at candidate
  next empty =>
    have same : before = after := Option.some.inj candidate
    subst after
    exact paths
  next nonempty =>
    split at candidate
    next recorded winner moved joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting)
          before.core (recorded, winner, moved) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedPaths := SourcePruningEnumerationTerminalPrefix.run_paths (P := P) r first rest before.waiting
        before.core joined recorded winner moved paths prefixSuccess
      rcases foldObserved : SourcePruningEnumerationCachedFold.run checkEmpty n p h recorded
          caller ⟨joined, before.expandable, moved⟩ winner queries with
        ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
      rw [foldObserved] at candidate
      have foldExact := (SourcePruningEnumerationCachedFold.erase checkEmpty n p h recorded
        caller ⟨joined, before.expandable, moved⟩ winner queries).symm.trans (congrArg Prod.fst foldObserved)
      have foldPaths := SourcePruningEnumerationFold.run_paths (P := P) checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedPaths foldExact
      cases foldResult with
      | error fault => cases candidate
      | ok possible =>
        cases possible with
        | none => cases candidate
        | some raw =>
          cases raw with
          | nil =>
            apply SourcePruningEnumerationCachedFold.candidate_paths (P := P) checkEmpty n p h recorded
              caller ⟨joined, before.expandable, moved⟩ winner queries joinedPaths after
            rw [foldObserved]
            exact candidate
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
                have foldedPaths : StatePaths P folded := by simpa only [foldedSame] using foldPaths
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
                      apply SourcePruningEnumerationIncomingCacheAdapter.observed_cache_paths (P := P) checkEmpty r n p h k
                        foldCaller (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs
                        foldQueries foldedPaths inputs after
                      rw [incomingObserved]
                      exact candidate
    next other => cases candidate

end SourcePruningEnumerationCachedTerminalAdapter

namespace SourcePruningEnumerationCachedPrepare

/-- Every actual cached child endpoint preserves its stored and supplied paths. -/
theorem cache_paths {EnumGuard NativeGuard : Type} {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs)
    (observed : (match prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) : StatePaths P after.core := by
  cases prepared : prepareChild heap fuel scs value before with
  | none => simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact paths
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              exact SourcePruningEnumerationPathStorage.prepareChild_paths (P := P)
                heap fuel scs value before paths inputs prepared (fragment, reached) (by simp)
          | cons row rest => simp only [prepared, reduceCtorEq] at observed

end SourcePruningEnumerationCachedPrepare

namespace SourcePruningEnumerationChildDispatch
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual retained candidate preserves the input path predicate. -/
theorem observed_cache_paths {P : EqualityTrie.Path → Prop}
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs) (after : Cached)
    (candidate : (run checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    StatePaths P after.core := by
  by_cases empty : incoming = .empty
  · simp only [run, empty, ↓reduceIte, Option.some.injEq] at candidate
    subst after
    exact paths
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        apply SourcePruningEnumerationCachedPrepare.cache_paths (P := P)
          caller.checked.native.machine.heap k scs incoming before after paths inputs
        simp only [run, ite_eq_right empty, partitioned] at candidate
        cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild
            caller.checked.native.machine.heap k scs incoming before with
        | none => simpa only [prepared] using candidate
        | some rows =>
          cases rows with
          | nil => simpa only [prepared] using candidate
          | cons row tail =>
            rcases row with ⟨fragment, reached⟩
            cases tail with
            | nil => simpa only [prepared] using candidate
            | cons next rest => simpa only [prepared] using candidate
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
        apply SourcePruningEnumerationCachedTerminalAdapter.candidate_paths (P := P) checkEmpty r n p h k
          first rest caller before incoming descendants queries paths descendantPaths after
        simpa only [run, ite_eq_right empty, partitioned] using candidate

end SourcePruningEnumerationChildDispatch
end MicroCFTA
