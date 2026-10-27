import MicroCFTA.SourceFlatPruningChildDispatch
import MicroCFTA.EnumerationFlatNativeTerminalCompletion
import MicroCFTA.SourcePruningEnumerationChildCompletion

/-!
# Flat observations of the complete native child producer

The original producer chooses its bounds before the flat input is supplied.
Each adequate native execution retains its own actual flat cache and raw core.
-/

namespace MicroCFTA.SourceFlatPruningChildCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationChildCompletion
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "FlatCore" => EnumerationFlatState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × Core))
variable {width : Nat}

private theorem rows_raw_related
    {flatRows : List (Fragment × FlatCached)} {oldRows : List (Fragment × Cached)}
    (related : SourceFlatPruningCachedPrepare.RowsRelated flatRows oldRows) :
    EnumerationResultRelation.Results (Error := EnumerationState.Error) EnumerationFlatState.Related
      (flatRows.map fun row => .ok (row.1, row.2.core))
      (oldRows.map fun row => .ok (row.1, row.2.core)) := by
  induction related with
  | nil => exact .nil
  | @cons left right lefts rights head _ ih =>
      obtain ⟨same, states⟩ := head
      simp only [List.map_cons]
      rw [same]
      exact .cons (.ok right.1 states.core) ih

private theorem rows_cache_related
    {flat : FlatCached} {before : Cached}
    {flatRows : List (Fragment × FlatCached)} {oldRows : List (Fragment × Cached)}
    (initial : EnumerationFlatCached.Related flat before)
    (related : SourceFlatPruningCachedPrepare.RowsRelated flatRows oldRows) :
    EnumerationFlatNativeIndex.WritesRelated
      (match flatRows with | [] => some flat | [(_, after)] => some after | _ => none)
      (match oldRows with | [] => some before | [(_, after)] => some after | _ => none) := by
  cases related with
  | nil => exact initial
  | cons head rest =>
      cases rest with
      | nil => exact head.2
      | cons _ _ => trivial

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem nonterminal_related
    {flat : FlatCached} {before : Cached}
    (related : EnumerationFlatCached.Related flat before)
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended) (incoming : Node)
    (caller : Caller width) (queries : Queries)
    (nonempty : incoming ≠ .empty) (descendants : List Suspended)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) = ([], descendants))
    (rows : List (Fragment × Cached))
    (prepared : SourcePruningEnumerationCachedPrepare.prepareChild
      caller.checked.native.machine.heap k bucket incoming before = some rows) :
    SourceFlatPruningChildDispatch.ResultRelated
      (SourceFlatPruningChildDispatch.run checkEmpty n p h bucket incoming caller flat queries)
      (SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller before queries) := by
  obtain ⟨next, flatPrepared, states⟩ :=
    SourceFlatPruningCachedPrepare.prepareChild_completed related
      caller.checked.native.machine.heap k bucket incoming prepared
  have oldErased := SourcePruningEnumerationCachedPrepare.erase_some
    caller.checked.native.machine.heap k bucket incoming before rows prepared
  obtain ⟨oldAction, oldActionEq, oldRaw⟩ := Option.map_eq_some_iff.mp oldErased
  have flatErased := SourceFlatPruningCachedPrepare.erase_some
    caller.checked.native.machine.heap bucket incoming flat next flatPrepared
  obtain ⟨flatAction, flatActionEq, flatRaw⟩ := Option.map_eq_some_iff.mp flatErased
  simp only [SourceFlatPruningChildDispatch.run, SourcePruningEnumerationChildDispatch.run,
    SourcePruningEnumerationChildDispatch.observe, ite_eq_right nonempty, partitioned,
    prepared, flatPrepared, oldActionEq, flatActionEq, oldRaw, flatRaw]
  exact ⟨⟨rfl, rfl, related.core, related.waiting, rows_raw_related states⟩,
    rows_cache_related related states⟩

private theorem terminal_waiting
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (recorded : List Nat) (winner : Nat)
    (moved : EnumerationWaitingIndex.Waiting) (joined : Core)
    (nonempty : incoming ≠ .empty)
    (prefixRun : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      r first rest before.waiting before.core) = [.ok ((recorded, winner, moved), joined)]) :
    (SourcePruningEnumerationCachedTerminalAdapter.run checkEmpty r n p h k
      first rest caller before incoming incomingScs queries).1.2.2.2.2 = moved := by
  rw [SourcePruningEnumerationCachedTerminalAdapter.erase]
  simp only [SourcePruningEnumerationTerminal.run, ite_eq_right nonempty, prefixRun]
  generalize SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries = folded
  obtain ⟨outcome, reached, saved, outer⟩ := folded
  cases outcome with
  | error fault => rfl
  | ok possible =>
    cases possible with
    | none => rfl
    | some rows =>
      cases rows with
      | nil => rfl
      | cons head tail =>
        cases head with
        | error fault => rfl
        | ok row =>
          obtain ⟨⟨⟩, after⟩ := row
          cases tail with
          | cons next rest => rfl
          | nil =>
            generalize SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
              reached after winner incoming incomingScs saved = observed
            obtain ⟨result, finalCaller, finalQueries, finalCore⟩ := observed
            cases result with
            | error fault => rfl
            | ok result => cases result <;> rfl

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem partition_subsets (bucket : List Suspended) (first : Suspended)
    (rest descendants : List Suspended)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants)) : (first :: rest) ⊆ bucket ∧ descendants ⊆ bucket := by
  have terminal : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
    simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
  have other : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) = descendants := by
    simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
  exact ⟨fun _ member => (List.mem_filter.mp (terminal ▸ member)).1,
    fun _ member => (List.mem_filter.mp (other ▸ member)).1⟩

/-- A stable original child observation gives the same actual flat native endpoint. -/
theorem observed
    (flat : FlatCached) (before : Cached) (related : EnumerationFlatCached.Related flat before)
    (checkEmpty : Bool) (r nativeFuel p h k : Nat) (bucket : List Suspended) (incoming : Node)
    (beforeCaller afterCaller : Caller width) (queries savedQueries : Queries)
    (raw : Raw) (after : Cached) (outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (roots : Nat → Nat) (safe : Safe before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (stable : ∀ extraRepresentative extraIndex,
      SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) nativeFuel p h
        (k + extraIndex) bucket incoming beforeCaller before queries =
        ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) :
    ∃ flatRows flatOuter recovered,
      SourceFlatPruningChildDispatch.run checkEmpty nativeFuel p h bucket incoming beforeCaller flat queries =
        ((.ok (some flatRows), afterCaller, savedQueries, flatOuter, waiting), some recovered) ∧
      EnumerationFlatCached.Related recovered after ∧
      EnumerationFlatState.Related flatOuter outer ∧
      EnumerationResultRelation.Results EnumerationFlatState.Related flatRows raw := by
  have correspondence : SourceFlatPruningChildDispatch.ResultRelated
      (SourceFlatPruningChildDispatch.run checkEmpty nativeFuel p h bucket incoming beforeCaller flat queries)
      ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
    by_cases empty : incoming = .empty
    · have earlier := stable 0 0
      simp only [Nat.add_zero] at earlier
      rw [← earlier, empty, SourceFlatPruningChildDispatch.empty,
        SourcePruningEnumerationChildDispatch.empty]
      exact ⟨⟨rfl, rfl, related.core, related.waiting, .nil⟩, related⟩
    · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
      | mk here descendants =>
        cases here with
        | nil =>
            have earlier := stable 0 0
            simp only [Nat.add_zero] at earlier
            cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild
                beforeCaller.checked.native.machine.heap k bucket incoming before with
            | none =>
                have candidate := congrArg Prod.snd earlier
                simp only [SourcePruningEnumerationChildDispatch.run, ite_eq_right empty,
                  partitioned, prepared] at candidate
                cases candidate
            | some rows =>
                have actual := nonterminal_related related checkEmpty r nativeFuel p h k bucket incoming
                  beforeCaller queries empty descendants partitioned rows prepared
                rw [earlier] at actual
                exact actual
        | cons first rest =>
            have subsets := partition_subsets bucket first rest descendants partitioned
            obtain ⟨prefixFuel, recorded, winner, moved, _scanned, _united, joined, prefixPacket⟩ :=
              SourcePruningEnumerationTerminalPrefix.run_complete
                beforeCaller.checked.native.machine.heap before.core first rest before.waiting roots
                paths counts safe (fun sc member => bounded sc (subsets.1 member))
                (fun held fragment stored sc member => pending held fragment stored sc (subsets.1 member)) realized
            have prefixRun : ∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
                (r + prefixFuel + extra) first rest before.waiting before.core) =
                [.ok ((recorded, winner, moved), joined)] := by
              intro extra
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using prefixPacket.1 (r + extra)
            have terminalRun : ∀ extraRepresentative extraIndex,
                SourcePruningEnumerationCachedTerminalAdapter.run checkEmpty
                  (r + prefixFuel + extraRepresentative) nativeFuel p h (k + extraIndex)
                  first rest beforeCaller before incoming descendants queries =
                  ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
              intro extraRepresentative extraIndex
              have actual := stable (prefixFuel + extraRepresentative) extraIndex
              rw [SourcePruningEnumerationChildDispatch.terminal checkEmpty _ _ _ _ _ bucket incoming
                beforeCaller before queries first rest descendants partitioned] at actual
              simpa only [Nat.add_assoc] using actual
            have waitingSame : waiting = moved := by
              have actual := congrArg (fun result => result.1.2.2.2.2) (terminalRun 0 0)
              simp only [Nat.add_zero] at actual
              rw [terminal_waiting checkEmpty (r + prefixFuel) nativeFuel p h k first rest
                beforeCaller before incoming descendants queries recorded winner moved joined empty
                (by simpa only [Nat.add_zero] using prefixRun 0)] at actual
              exact actual.symm
            obtain ⟨flatRows, flatOuter, recovered, actual, cacheRelated, outerRelated, rowsRelated⟩ :=
              EnumerationFlatNativeTerminal.observed related first rest (r + prefixFuel) recorded winner
                moved joined prefixRun checkEmpty nativeFuel p h k beforeCaller afterCaller incoming descendants
                queries savedQueries raw outer after (by simpa only [waitingSame] using terminalRun)
            have actualChild : SourceFlatPruningChildDispatch.run checkEmpty nativeFuel p h bucket incoming
                beforeCaller flat queries =
                ((.ok (some flatRows), afterCaller, savedQueries, flatOuter, waiting), some recovered) := by
              simpa only [SourceFlatPruningChildDispatch.run, ite_eq_right empty, partitioned, waitingSame]
                using actual
            rw [actualChild]
            exact ⟨⟨rfl, rfl, outerRelated, rfl, rowsRelated⟩, cacheRelated⟩
  generalize actual : SourceFlatPruningChildDispatch.run checkEmpty nativeFuel p h
      bucket incoming beforeCaller flat queries = actualResult at correspondence
  obtain ⟨⟨outcome, reachedCaller, returnedQueries, flatOuter, returnedWaiting⟩, recovered⟩ := actualResult
  obtain ⟨⟨callerSame, queriesSame, outerRelated, waitingSame, rowsRelated⟩, cacheRelated⟩ := correspondence
  dsimp only at callerSame queriesSame outerRelated waitingSame rowsRelated cacheRelated
  subst reachedCaller returnedQueries returnedWaiting
  cases recovered with
  | none => cases cacheRelated
  | some recovered =>
      cases outcome with
      | error fault =>
          cases fault with
          | inl prefixFault => cases rowsRelated
          | inr remaining => cases remaining <;> cases rowsRelated
      | ok returned =>
          cases returned with
          | none => cases rowsRelated
          | some flatRows =>
              exact ⟨flatRows, flatOuter, recovered, rfl, cacheRelated, outerRelated, rowsRelated⟩

/-- Retain the complete old child packet and append each actual flat execution. -/
theorem complete_with_fragments
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (ranges : Ranges checkEmpty bucket incoming beforeCaller before memos.query) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller width) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) bucket incoming beforeCaller before memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed bucket →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
        PendingFragment after.core fragment ∧
        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
          Avoids before.core.representatives held bucket →
          FragmentAvoid after.core.representatives held fragment)) ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ extraNative P H, p ≤ P → h ≤ H →
        ∃ flatRows flatOuter recovered,
          SourceFlatPruningChildDispatch.run checkEmpty (n + extraNative) P H
            bucket incoming beforeCaller flat memos.query =
            ((.ok (some flatRows), afterCaller, savedQueries, flatOuter, waiting), some recovered) ∧
          EnumerationFlatCached.Related recovered after ∧
          EnumerationFlatState.Related flatOuter outer ∧
          EnumerationResultRelation.Results EnumerationFlatState.Related flatRows raw ∧
          EnumerationFlatNativeIndex.Correct afterCaller.checked.native.machine.heap recovered) := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, packet⟩ :=
    SourcePruningEnumerationChildCompletion.complete_with_fragments formulas solver inventory
      beforeCaller before checkEmpty bucket incoming roots memos initial safe paths counts flags
      realized bounded pending available closed ranges
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, packet, ?_⟩
  obtain ⟨stable, _post, _querySame, _growth, afterPaths, storage, _afterRealized,
    afterCounts, afterFlags, _origin, _protects, _references, _history, _shape⟩ := packet
  intro flat related extraNative P H enoughP enoughH
  obtain ⟨flatRows, flatOuter, recovered, actual, cacheRelated, outerRelated, rowsRelated⟩ :=
    observed flat before related checkEmpty r (n + extraNative) P H k bucket incoming
      beforeCaller afterCaller memos.query savedQueries raw after outer waiting roots safe paths counts
      realized bounded pending (fun extraRepresentative extraIndex =>
        stable extraRepresentative extraNative P H extraIndex enoughP enoughH)
  exact ⟨flatRows, flatOuter, recovered, actual, cacheRelated, outerRelated, rowsRelated,
    EnumerationFlatNativeIndex.correct_of_related cacheRelated afterCaller.checked.native.machine.heap
      afterRoots afterPaths storage.aligned afterFlags afterCounts⟩

end MicroCFTA.SourceFlatPruningChildCompletion
