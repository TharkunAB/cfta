import MicroCFTA.SourceCurrentCachedPrepareRowsObserved
import MicroCFTA.SourcePruningEnumerationChildDispatch
import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion

/-! The literal no-terminal dispatch retains its caller and validates every returned cache. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentChildDispatchNonterminalCache
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}

open scoped Classical in
/-- Every actual returned no-terminal cache is valid at the exact returned caller. -/
theorem nonterminal_dispatch_valid (caller : Caller width) (before : Cached)
    (queries : SourceEndpointMemo.Memos) (scs : List Suspended) (incoming : Node)
    (checkEmpty : Bool) (r n p h k : Nat)
    (valid : CacheValid caller before)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (available : InternedProbeProvenance.Available caller.checked.native.machine.heap incoming)
    (closed : incoming.free = []) (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) :
    let actual := SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming caller before queries
    match (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 with
    | [] => actual.1.2.1 = caller ∧ actual.1.2.2.1 = queries ∧
        ∀ after, actual.2 = some after → CacheValid actual.1.2.1 after
    | _ :: _ => True := by
  dsimp only
  cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk terminals descendants =>
      cases terminals with
      | cons first rest => trivial
      | nil =>
          by_cases empty : incoming = .empty
          · simp only [SourcePruningEnumerationChildDispatch.run, ite_eq_left empty]
            refine ⟨True.intro, True.intro, ?_⟩
            intro after observed
            have cacheEq : before = after := Option.some.inj observed
            cases cacheEq
            exact valid
          · simp only [SourcePruningEnumerationChildDispatch.run, ite_eq_right empty, partitioned]
            have reached : (SourcePruningEnumerationChildDispatch.observe checkEmpty r n p h scs incoming
                caller before.core before.waiting queries).2.1 = caller := by
              simp only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty, partitioned]
              cases SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming <;> rfl
            have saved : (SourcePruningEnumerationChildDispatch.observe checkEmpty r n p h scs incoming
                caller before.core before.waiting queries).2.2.1 = queries := by
              simp only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty, partitioned]
              cases SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming <;> rfl
            refine ⟨reached, saved, ?_⟩
            intro after observed
            rw [reached]
            cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
                k scs incoming before with
            | none => simp [prepared] at observed
            | some rows =>
                cases rows with
                | nil =>
                    have cacheEq : before = after := by
                      simpa only [prepared, Option.some.injEq] using observed
                    cases cacheEq
                    exact valid
                | cons row tail =>
                    cases tail with
                    | cons second rest => simp [prepared] at observed
                    | nil =>
                        rcases row with ⟨fragment, produced⟩
                        have cacheEq : produced = after := by
                          simpa only [prepared, Option.some.injEq] using observed
                        rw [← cacheEq]
                        obtain ⟨roots, paths, storage, realized, counts, flags⟩ := valid
                        obtain ⟨storageAfter, realizedAfter, pathsAfter, countsAfter, flagsAfter⟩ :=
                          SourceCurrentCachedPrepareRowsObserved.prepare_child_row_valid
                            caller.checked.native.machine.heap before produced scs incoming roots coherent available
                            closed storage realized paths counts flags bounded k fragment [(fragment, produced)]
                            prepared (List.mem_cons_self)
                        exact ⟨roots, pathsAfter, storageAfter, realizedAfter, countsAfter, flagsAfter⟩

end MicroCFTA.SourceCurrentChildDispatchNonterminalCache
