import MicroCFTA.SourcePruningEnumerationTerminalCarriers
import MicroCFTA.SourcePruningEnumerationPreparedCarriers
import MicroCFTA.SourcePruningEnumerationChildDispatch

/-!
# Graph carriers in actual child dispatch

Every attached candidate retains the carriers of its input cache.
Every successful singleton supplies the holes in its returned fragment.
The shallow route retains the original forest. The terminal route uses actual class unions.
-/
namespace MicroCFTA.SourcePruningEnumerationShallowChild
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

private theorem prepared_representatives
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : prepareChild scs value = some action)
    (success : Success action before fragment after) :
    after.representatives = before.representatives := by
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
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have writtenSame := (EnumerationDriver.modify_success _
          (allocated (some (entry.identity + 1)) before) written).mp writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        rw [writtenSame]
        rfl
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
        rfl

end MicroCFTA.SourcePruningEnumerationShallowChild

namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCarriers EnumerationGraphReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

private theorem rows_total
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (rows : List (Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    (total : UnionFind.Total before.core.representatives)
    (cached : prepareChild heap fuel scs value before = some rows) :
    ∀ fragment after, (fragment, after) ∈ rows → UnionFind.Total after.core.representatives := by
  have raw := erase_some heap fuel scs value before rows cached
  cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := EnumGuard) scs value with
  | none => simp only [prepared, Option.map_none, reduceCtorEq] at raw
  | some action =>
      simp only [prepared, Option.map_some, Option.some.injEq] at raw
      intro fragment after member
      have success : Success action before.core fragment after.core := by
        rw [Success, raw]
        exact List.mem_map.mpr ⟨(fragment, after), member, rfl⟩
      rw [SourcePruningEnumerationShallowChild.prepared_representatives
        scs value before.core after.core action fragment prepared success]
      exact total

/-- Every actual shallow candidate retains old carriers, including empty rejection. -/
theorem cache_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (safe : Safe before.core) (references : ReferencesCarry before.core)
    (observed : (match prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  cases prepared : prepareChild heap fuel scs value before with
  | none => simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact ⟨safe.1.total, .refl _, references⟩
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              have facts := rows_carriers heap fuel scs value before [(fragment, reached)]
                safe references prepared fragment reached (by simp)
              exact ⟨rows_total heap fuel scs value before [(fragment, reached)] safe.1.total
                prepared fragment reached (by simp), facts.1, facts.2.1⟩
          | cons row rest => simp only [prepared, reduceCtorEq] at observed

end MicroCFTA.SourcePruningEnumerationCachedPrepare

namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCarriers EnumerationGraphReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual attached child cache retains its input carriers and references. -/
theorem candidate_carriers
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (safe : Safe before.core) (references : ReferencesCarry before.core) (after : Cached)
    (candidate : (run checkEmpty r n p h k scs incoming caller before queries).2 = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  by_cases empty : incoming = .empty
  · have same : before = after := by simpa only [run, empty, ↓reduceIte, Option.some.injEq] using candidate
    subst after
    exact ⟨safe.1.total, .refl _, references⟩
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
          apply SourcePruningEnumerationCachedPrepare.cache_carriers
            caller.checked.native.machine.heap k scs incoming before after safe references
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
          apply SourcePruningEnumerationCachedTerminalAdapter.candidate_carriers
            checkEmpty r n p h k first rest caller before incoming descendants queries
            safe.1.total references after
          simpa only [run, empty, ↓reduceIte, partitioned] using candidate

/-- Every successful child singleton supplies graph carriers for its exact returned fragment. -/
theorem successful_carriers
    {checkEmpty : Bool} {r n p h k : Nat} {scs : List Suspended} {incoming : Node}
    {caller reachedCaller : Caller width} {before after : Cached} {queries savedQueries : Queries}
    {fragment : Fragment} {returned outer : Core} {waiting : EnumerationWaitingIndex.Waiting}
    (safe : Safe before.core) (references : ReferencesCarry before.core)
    (observed : run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core ∧ FragmentCarries after.core fragment := by
  have candidateFacts := candidate_carriers checkEmpty r n p h k scs incoming caller before queries
    safe references after (by rw [observed])
  refine ⟨candidateFacts.1, candidateFacts.2.1, candidateFacts.2.2, ?_⟩
  have coreSame := singleton_core checkEmpty r n p h k scs incoming caller reachedCaller before after
    queries savedQueries fragment returned outer waiting observed
  rw [coreSame]
  have original := (erase checkEmpty r n p h k scs incoming caller before queries).symm.trans
    (congrArg Prod.fst observed)
  by_cases empty : incoming = .empty
  · simp only [observe, empty, ↓reduceIte] at original
    cases original
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
          simp only [observe, empty, ↓reduceIte, partitioned] at original
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
          | none => simp only [prepared] at original; cases original
          | some action =>
              rw [prepared] at original
              have rawSame := congrArg Prod.fst original
              dsimp only at rawSame
              have success : Success action before.core fragment returned := by
                rw [Success, Option.some.inj (Except.ok.inj rawSame)]
                exact List.mem_singleton_self _
              exact (SourcePruningEnumerationShallowChild.prepared_carriers scs incoming before.core
                returned action fragment safe references prepared success).2.2
      | cons first rest =>
          apply (SourcePruningEnumerationTerminal.successful_carriers checkEmpty r n p h first rest
            before.waiting caller before.core incoming descendants queries fragment reachedCaller
            savedQueries outer returned waiting safe.1.total references ?_).2.2.2
          simpa only [observe, empty, ↓reduceIte, partitioned] using original

end MicroCFTA.SourcePruningEnumerationChildDispatch
