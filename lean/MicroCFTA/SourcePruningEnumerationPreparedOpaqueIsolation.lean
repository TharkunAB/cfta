import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationCreatedIsolation
import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation

/-!
# An actual top-level opaque completion retains a fresh boundary

The proof consumes one actual completion at its original work fuel.
It does not require a stable family or another resource reservation.
The actual child allocates the fresh marker. The actual captured-slot
finalizer changes a different slot and retains the isolated marker.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
open EnumerationDischargeHistory
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {Typing : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual nonterminal opaque completion of a closed value must be a recursive boundary. -/
theorem complete_boundary_of_nonterminal
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries) (fragment : Fragment)
    (closed : value.free = [])
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (observed : run checkEmpty r n p h k target scs value caller before queries =
      some (.complete fragment reached saved after)) :
    MergedOrdinaryHeight.recursiveBoundary value = true := by
  cases value with
  | empty => simp only [run, ↓reduceIte, Option.some.injEq, reduceCtorEq] at observed
  | reference name => cases closed
  | node entry edges depth free => simp [run, nonterminal] at observed
  | union entry members depth free | mu entry members depth free => rfl

/-- A completed actual nonterminal opaque arm has an isolated fresh boundary at its own endpoint. -/
theorem complete_opaque_isolated
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (inside : target < before.core.counter)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
    (observed : run checkEmpty r n p h k target scs value caller before memos.query =
      some (.complete fragment reached saved after)) :
    reached = caller ∧ saved = memos.query ∧ fragment = .hole before.core.counter ∧
      ∃ handle, encodeNode value = some handle ∧
        lookupNode reached.checked.native.machine.heap handle = some value ∧
        IsolatedPending before.core.counter handle after.core := by
  have nonempty : value ≠ .empty := by
    intro same
    subst value
    cases boundary
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨handle, action, middle, encoded, decoded, prepared, cachedRun, raw, middleCore,
    _freshStored, _growth, _aligned, _forest, _middlePaths, _middleStorage, _middleRealized,
    _middleCounts, _waitingSame, _flagSame, _middleFlags, _holeBound⟩ :=
    SourcePruningEnumerationCachedPrepare.boundary_complete caller.checked.native.machine.heap before
      value scs roots packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent available closed
      boundary nonterminal storage realized paths counts flags
  have noHere : (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
    simp only [List.partition_eq_filter_filter]
    exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp nonterminal sc member)
  have childRun : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs value caller before memos.query =
      ((.ok (some [.ok (.hole before.core.counter, middle.core)]), caller, memos.query,
        before.core, before.waiting), some middle) := by
    cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      have hereSame : here = [] := by simpa only [partitioned] using noHere
      subst here
      simp only [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
        ite_eq_right nonempty, partitioned, prepared, cachedRun k, raw]
  have finishingObserved :
      (SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap k target
        (.hole before.core.counter) middle).map
        (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete
          (.hole before.core.counter) caller memos.query finished) =
        some (.complete fragment reached saved after) := by
    cases value <;> cases boundary
    all_goals
      simpa only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte, childRun] using observed
  obtain ⟨finished, finishing, same⟩ := Option.map_eq_some_iff.mp finishingObserved
  obtain ⟨fragmentSame, callerSame, querySame, afterSame⟩ :=
    SourcePruningEnumerationSelectedEdge.Result.complete.inj same
  subst fragment reached saved after
  have created : IsolatedPending before.core.counter handle middle.core := by
    rw [middleCore]
    exact allocated_isolated before.core handle packet.safe
  have different : target ≠ before.core.counter := Nat.ne_of_lt inside
  exact ⟨rfl, rfl, rfl, handle, encoded, decoded,
    created.through_finalize caller.checked.native.machine.heap k target before.core.counter handle
      (.hole before.core.counter) middle finished different finishing⟩

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
