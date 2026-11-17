import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations

namespace MicroCFTA.SourcePruningEnumerationSharedShallowFootprint
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
set_option autoImplicit false

/- Note [Observed shallow child footprint]
The actual successful receipt fixes the action and cached endpoint.
The raw action allocates the original counter and returns that hole.
An ordinary node then writes the complete input bucket.
Mu and Union return the allocation without that bucket write.
The native classification supplies its actual decoded value.
No equality between that value and the full incoming payload is assumed.
The pending owner is fresh when the original counter equals the slot count.
The conclusion states this condition explicitly. It is not an extra premise.
See Note [Original path occurrence at a child invocation] in
MicroCFTA.SourcePruningEnumerationSelectedPathDescent.
-/

private theorem prepared_success_shape
    (scs : List Suspended) (incoming : Node) (before returned : Core)
    (action : EnumerateM Symbol Constraint Fragment) (fragment : Fragment)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (success : Success action before fragment returned) :
    ∃ handle, encodeNode incoming = some handle ∧ fragment = .hole before.counter ∧
      returned = (match incoming with
        | .node _ _ _ _ =>
            {allocated (some handle) before with
              values := (allocated (some handle) before).values.set before.counter
                (.unenumerated (some handle) scs)}
        | _ => allocated (some handle) before) := by
  cases incoming with
  | empty =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      exact (EnumerationSchedule.reject_unsuccessful before returned fragment success).elim
  | reference name =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, reduceCtorEq] at prepared
  | node entry edges depth free =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal, Bool.false_eq_true,
        ↓reduceIte, encodeNode, Option.some.injEq] at prepared
      rw [← prepared] at success
      obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
      have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
        simpa [Success, allocate_exact, ExceptT.run] using allocation
      obtain ⟨rfl, rfl⟩ := shape
      obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      have writtenSame := (EnumerationDriver.modify_success _
        (allocated (some (entry.identity + 1)) before) written).mp writing
      obtain ⟨fragmentSame, afterSame⟩ :=
        (success_pure (.hole before.counter) fragment written returned).mp final
      exact ⟨entry.identity + 1, rfl, fragmentSame, afterSame.trans writtenSame⟩
  | union entry _ _ _ | mu entry _ _ _ =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal, Bool.false_eq_true,
        ↓reduceIte, encodeNode, Option.some.injEq] at prepared
      rw [← prepared] at success
      obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
      have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
        simpa [Success, allocate_exact, ExceptT.run] using allocation
      obtain ⟨rfl, rfl⟩ := shape
      obtain ⟨fragmentSame, afterSame⟩ :=
        (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) returned).mp final
      exact ⟨entry.identity + 1, rfl, fragmentSame, afterSame⟩

private theorem allocation_readback
    (heap : InternedConstructorTemplates.State Symbol Constraint) (handle : Nat)
    (before : Cached) (allocation : Nat × Cached)
    (actual : SourcePruningEnumerationCachedChild.allocate heap (some handle) before = some allocation) :
    ∃ (decoded : Node) (flag : Bool), lookupNode heap handle = some decoded ∧
      SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated (some handle) []) = some flag := by
  unfold SourcePruningEnumerationCachedChild.allocate at actual
  obtain ⟨flag, classified, _same⟩ := Option.map_eq_some_iff.mp actual
  have nativeRead := classified
  simp only [SourcePruningEnumerationNativeIndex.candidate, Option.map_eq_some_iff] at nativeRead
  obtain ⟨decoded, found, _classifiedValue⟩ := nativeRead
  exact ⟨decoded, flag, found, classified⟩

private theorem cached_success_readback
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List Suspended) (incoming : Node) (before after : Cached) (fragment : Fragment)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (actual : SourcePruningEnumerationCachedPrepare.prepareChild heap fuel scs incoming before =
      some [(fragment, after)]) :
    ∃ (handle : Nat) (decoded : Node) (flag : Bool),
      encodeNode incoming = some handle ∧ lookupNode heap handle = some decoded ∧
      SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated (some handle) []) = some flag := by
  cases incoming with
  | empty =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild, Option.some.injEq, reduceCtorEq] at actual
  | reference name =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild, reduceCtorEq] at actual
  | node entry edges depth free =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild, Option.map_eq_some_iff] at actual
      obtain ⟨result, prepared, _rowsSame⟩ := actual
      simp only [SourcePruningEnumerationCachedChild.prepareOrdinary, nonterminal, Bool.false_eq_true,
        ↓reduceIte, encodeNode, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at prepared
      obtain ⟨allocation, allocated, _written, _writing, _resultSame⟩ := prepared
      obtain ⟨decoded, flag, found, classified⟩ := allocation_readback heap (entry.identity + 1) before allocation allocated
      exact ⟨entry.identity + 1, decoded, flag, rfl, found, classified⟩
  | union entry _ _ _ | mu entry _ _ _ =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild, nonterminal, Bool.false_eq_true,
        ↓reduceIte, encodeNode, Option.bind_some, Option.map_eq_some_iff] at actual
      obtain ⟨allocation, allocated, _rowsSame⟩ := actual
      obtain ⟨decoded, flag, found, classified⟩ := allocation_readback heap (entry.identity + 1) before allocation allocated
      exact ⟨entry.identity + 1, decoded, flag, rfl, found, classified⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem nonterminal_success_footprint
    (checkEmpty : Bool) (r n p h k : Nat)
    (scs : List Suspended) (incoming : Node) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (fragment : Fragment)
    (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
      ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after)) :
    let storedBucket : List Suspended := match incoming with | .node _ _ _ _ => scs | _ => []
    ∃ (handle : Nat) (decoded : Node) (flag : Bool)
        (action : EnumerateM Symbol Constraint Fragment),
      incoming ≠ .empty ∧
      SourcePruningEnumerationNodes.encodeNode incoming = some handle ∧
      SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some decoded ∧
      SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        (.unenumerated (some handle) []) = some flag ∧
      SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action ∧
      ExceptT.run (action before.core) = [.ok (fragment, returned)] ∧
      SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
        k scs incoming before = some [(fragment, after)] ∧
      fragment = .hole before.core.counter ∧ reached = caller ∧ saved = queries ∧
      read = before.core ∧ waiting = before.waiting ∧ after.core = returned ∧
      returned = (match incoming with
        | .node _ _ _ _ =>
            {EnumerationState.allocated (some handle) before.core with
              values := (EnumerationState.allocated (some handle) before.core).values.set
                before.core.counter (.unenumerated (some handle) scs)}
        | _ => EnumerationState.allocated (some handle) before.core) ∧
      after.core.counter = before.core.counter + 1 ∧
      (before.core.counter = before.core.values.length →
        after.core.values[before.core.counter]? = some (.unenumerated (some handle) storedBucket) ∧
          after.core.counter = after.core.values.length)
 := by
  dsimp only
  have nonempty : incoming ≠ .empty := by
    intro empty
    simp only [ChildDispatch.run, empty, ↓reduceIte, Prod.mk.injEq,
      Except.ok.injEq, Option.some.injEq, reduceCtorEq, false_and] at actual
  have noHere : (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
    simp only [List.partition_eq_filter_filter]
    exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp nonterminal sc member)
  have coreSame := ChildDispatch.singleton_core checkEmpty r n p h k scs incoming caller reached
    before after queries saved fragment returned read waiting actual
  cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
      have hereSame : here = [] := by simpa only [partitioned] using noHere
      subst here
      have observed : ChildDispatch.observe checkEmpty r n p h scs incoming caller before.core
          before.waiting queries = (.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting) :=
        (ChildDispatch.erase checkEmpty r n p h k scs incoming caller before queries).symm.trans
          (congrArg Prod.fst actual)
      cases prepared : SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) scs incoming with
      | none =>
          simp only [ChildDispatch.observe, ite_eq_right nonempty, partitioned, prepared,
            Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at observed
      | some action =>
          have endpoints : ExceptT.run (action before.core) = [.ok (fragment, returned)] ∧
              caller = reached ∧ queries = saved ∧ before.core = read ∧ before.waiting = waiting := by
            simpa only [ChildDispatch.observe, ite_eq_right nonempty, partitioned, prepared,
              Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] using observed
          obtain ⟨raw, callerSame, queriesSame, readSame, waitingSame⟩ := endpoints
          have cachedSingleton : SourcePruningEnumerationCachedPrepare.prepareChild
              caller.checked.native.machine.heap k scs incoming before = some [(fragment, after)] := by
            cases cached : SourcePruningEnumerationCachedPrepare.prepareChild
                caller.checked.native.machine.heap k scs incoming before with
            | none =>
                have cacheReturned := congrArg Prod.snd actual
                simp only [ChildDispatch.run, ite_eq_right nonempty, partitioned, cached, reduceCtorEq] at cacheReturned
            | some rows =>
                have erasure := SourcePruningEnumerationCachedPrepare.erase_some
                  caller.checked.native.machine.heap k scs incoming before rows cached
                rw [prepared, Option.map_some, raw] at erasure
                have rowsMapped : rows.map (fun row => Except.ok (row.1, row.2.core)) =
                    [.ok (fragment, returned)] := (Option.some.inj erasure).symm
                obtain ⟨row, _singleton, mapped⟩ := List.map_eq_singleton_iff.mp rowsMapped
                rcases row with ⟨childFragment, childCache⟩
                subst rows
                have cacheSame : childCache = after := by
                  simpa only [ChildDispatch.run, ite_eq_right nonempty, partitioned, cached,
                    Option.some.injEq] using congrArg Prod.snd actual
                have fragmentSame : childFragment = fragment := (Prod.mk.inj (Except.ok.inj mapped)).1
                rw [← cacheSame, ← fragmentSame]
          have success : Success action before.core fragment returned := by
            simp only [Success, raw, List.mem_singleton]
          obtain ⟨handle, encoded, fragmentSame, returnedShape⟩ :=
            prepared_success_shape scs incoming before.core returned action fragment nonterminal prepared success
          obtain ⟨observedHandle, decoded, flag, observedEncoded, nativeRead, classified⟩ :=
            cached_success_readback caller.checked.native.machine.heap k scs incoming before after fragment
              nonterminal cachedSingleton
          have handleSame : observedHandle = handle := Option.some.inj (observedEncoded.symm.trans encoded)
          subst observedHandle
          have scalars : after.core.counter = before.core.counter + 1 ∧
              (before.core.counter = before.core.values.length →
                after.core.values[before.core.counter]? = some (.unenumerated (some handle)
                  (match incoming with | .node _ _ _ _ => scs | _ => [])) ∧
                  after.core.counter = after.core.values.length) := by
            cases incoming with
            | node entry edges depth free =>
                rw [coreSame, returnedShape]
                refine ⟨rfl, ?_⟩
                intro aligned
                have inside : before.core.counter < (allocated (some handle) before.core).values.length := by
                  simp only [allocated, List.length_append, List.length_singleton, ← aligned]
                  exact Nat.lt_succ_self _
                exact ⟨List.getElem?_set_self inside, by
                  simpa only [List.length_set] using allocated_supply (some handle) before.core aligned⟩
            | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                rw [coreSame, returnedShape]
                exact ⟨rfl, fun aligned =>
                  ⟨allocated_slot (some handle) before.core aligned,
                    allocated_supply (some handle) before.core aligned⟩⟩
          cases incoming <;>
            exact ⟨handle, decoded, flag, action, nonempty, encoded, nativeRead, classified,
              rfl, raw, cachedSingleton, fragmentSame, callerSame.symm, queriesSame.symm,
              readSame.symm, waitingSame.symm, coreSame, returnedShape, scalars.1, scalars.2⟩

end MicroCFTA.SourcePruningEnumerationSharedShallowFootprint
