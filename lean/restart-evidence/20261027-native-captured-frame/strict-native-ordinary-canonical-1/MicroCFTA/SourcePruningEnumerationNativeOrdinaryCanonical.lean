import MicroCFTA.SourcePruningEnumerationNativeOrdinary
import MicroCFTA.SourcePruningEnumerationNativeBranchCanonical
import MicroCFTA.SourcePruningEnumerationEntryCanonical

/-!
# Canonical storage after actual native ordinary entry

Entry supplies its actual stored bucket and representative paths.
Its ancestry update is not a full compression Frame.
Each completed alternative retains its own canonical enumeration cache.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeOrdinary
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationValidity
open InternedConstructorTemplates SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList

private theorem enter_paths
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv : Nat)
    (before after : Core) (target handle : Nat) (bucket : List Suspended) (decoded : Node)
    (total : UnionFind.Total before.representatives)
    (success : Success (SourcePruningEnumerationEntry.enter heap fuel uv)
      before (target, handle, bucket, decoded) after) :
    ∀ slot root size, UnionFind.Reaches after.representatives slot root size ↔
      UnionFind.Reaches before.representatives slot root size := by
  unfold SourcePruningEnumerationEntry.enter at success
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  have readFrame := (EnumerationCompressionFrame.getValue_frame fuel uv before read value total reading).1
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have fullFrame := readFrame.trans
            (EnumerationCompressionFrame.representative_frame fuel uv found read compressed
              (readFrame.total total) compressing)
          cases lookup : lookupNode heap storedHandle with
          | none =>
              simp only [lookup] at continued
              exact (success_failure .unresolvedReference compressed after _ continued).elim
          | some actual =>
              simp only [lookup] at continued
              obtain ⟨ignored, entered, modifying, final⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
              obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
              exact fullFrame.reaches

/-- The actual entry row and existing prefix Posts certify each completed alternative cache. -/
theorem observed_canonical
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (canonical : Canonical before.core)
    {r n p h k : Nat} (entered : Cached) (result : Result width)
    (stable : EnumerationDriver.RenderStable before.core entered.core)
    (sameFlags : entered.expandable = before.expandable)
    (sameWaiting : entered.waiting = before.waiting)
    (observed : run checkEmpty r n p h k uv edgesOf caller before memos.query =
      ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)], some result))
    (receiptPosts : ∀ receipt ∈ SourcePruningEnumerationNativeBranchCompletion.processedReceipts result,
      ∃ (reached : Caller width) (saved : Queries) (next : Inventory) (final : Memos),
        SourcePruningEnumerationNativeBranches.advance receipt = some (reached, saved) ∧
        Post formulas solver next caller reached final ∧ final.query = saved) :
    Canonical entered.core ∧
      ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
        .complete fragment reached saved after ∈
          SourcePruningEnumerationNativeBranchCompletion.processedReceipts result → Canonical after.core := by
  have actualEntry := congrArg Prod.fst observed
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
    [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)] at actualEntry
  have success : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv)
      before.core (uv, handle, scs, .node parentEntry storedEdges depth free) entered.core := by
    rw [Success, actualEntry]
    exact List.mem_singleton_self _
  have enteredCanonical := (SourcePruningEnumerationEntry.enter_canonical caller.checked.native.machine.heap
    r uv before.core entered.core uv handle scs (.node parentEntry storedEdges depth free) canonical success).1
  have reachedPaths := enter_paths caller.checked.native.machine.heap r uv before.core entered.core
    uv handle scs (.node parentEntry storedEdges depth free) ready.safe.1.total success
  have enteredStored : entered.core.values[uv]? = some (.unenumerated (some handle) scs) := by
    simpa only [stable.values] using stored
  have enteredReady : EnumerationDriver.Ready uv entered.core := by
    refine ⟨stable.safe, by simpa only [stable.counter] using ready.inside, ?_, ?_⟩
    · exact (stable.safe.2 uv _ enteredStored).mp (by intro impossible; cases impossible)
    · intro node bucket currentStored sc member sameClass
      exact ready.avoids node bucket (by simpa only [stable.values] using currentStored) sc member
        ((stable.classes uv sc.var).mp sameClass)
  have enteredRoots : Roots entered.core.representatives roots := by
    intro slot
    obtain ⟨size, path⟩ := paths slot
    exact ⟨size, (reachedPaths slot (roots slot) size).mpr path⟩
  have enteredRealized : PendingRealized caller.checked.native.machine.heap entered.core := by
    intro slot node bucket currentStored
    exact realized slot node bucket (by simpa only [stable.values] using currentStored)
  have enteredCounts : EnumerationCanonicalWaiting.Correct roots entered.core.values entered.waiting := by
    simpa only [stable.values, sameWaiting] using counts
  have enteredFlags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((entered.core.values[slot]?).getD .eliminated) = some (entered.expandable slot) := by
    simpa only [stable.values, sameFlags] using flags
  have enteredPending : InputsPending entered.core scs := by
    intro held fragment expanded sc member sameClass
    exact pending held fragment (by simpa only [stable.values] using expanded) sc member
      ((stable.classes held sc.var).mp sameClass)
  have frame : EnumerationExpandableIndex.frame entered.core before = entered := by
    cases entered with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact sameFlags.symm
        · exact sameWaiting.symm
  have actualScan := congrArg Prod.snd observed
  simp only [run, actualEntry, nonterminal, Bool.false_eq_true, ite_false, frame] at actualScan
  refine ⟨enteredCanonical, ?_⟩
  exact SourcePruningEnumerationNativeBranchCompletion.observed_canonical formulas solver inventory caller entered
    checkEmpty uv handle scs parentEntry storedEdges (edgesOf (.node parentEntry storedEdges depth free))
    depth free roots memos initial enteredReady enteredStored decoded enteredRealized selected enteredRoots
    enteredCounts enteredFlags enteredPending enteredCanonical (Option.some.inj actualScan) receiptPosts

/-- The original stable ordinary producer retains its complete receipt prefix and adds canonical caches. -/
theorem complete_with_history_canonical
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (ranges : Ranges checkEmpty uv edgesOf caller before memos.query)
    (canonical : Canonical before.core) :
    ∃ (r n p h k : Nat) (entered : Cached) (processed : List (Receipt width))
      (afterCaller : Caller width) (saved : Queries) (final : Memos) (next : Inventory) (result : Result width),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv edgesOf caller before memos.query =
          ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)], some result)) ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Pending receipt) ∧
      (∀ receipt ∈ processed,
        ∃ (reached : Caller width) (savedQueries : Queries) (receiptInventory : Inventory) (receiptMemos : Memos),
          SourcePruningEnumerationNativeBranches.advance receipt = some (reached, savedQueries) ∧
          Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
      (∀ receipt ∈ processed,
        SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      Canonical entered.core ∧
      (∀ (fragment : Fragment) (reached : Caller width) (queries : Queries) (after : Cached),
        .complete fragment reached queries after ∈ processed → Canonical after.core) := by
  obtain ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    observed, stable, sameFlags, sameWaiting, post, querySame, admitted, pendingHistory,
    receiptPosts, fragmentHistory, shape, supported⟩ :=
    complete_with_history formulas solver inventory caller before checkEmpty uv handle scs parentEntry
      storedEdges depth free edgesOf roots memos initial ready stored decoded realized selected paths counts flags
      pending nonterminal ranges
  have receiptView : SourcePruningEnumerationNativeBranchCompletion.processedReceipts result = processed := by
    rcases shape with completed | stopped
    · rw [completed]
      rfl
    · rw [stopped]
      rfl
  have actual : run checkEmpty r n p h k uv edgesOf caller before memos.query =
      ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)], some result) := by
    simpa only [Nat.add_zero] using observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨enteredCanonical, branchCanonical⟩ := observed_canonical formulas solver inventory caller before
    checkEmpty uv handle scs parentEntry storedEdges depth free edgesOf roots memos initial ready stored decoded
    realized selected paths counts flags pending nonterminal canonical entered result stable sameFlags sameWaiting
    actual (by simpa only [receiptView] using receiptPosts)
  refine ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    observed, stable, sameFlags, sameWaiting, post, querySame, admitted, pendingHistory,
    receiptPosts, fragmentHistory, shape, supported, enteredCanonical, ?_⟩
  simpa only [receiptView] using branchCanonical

end MicroCFTA.SourcePruningEnumerationNativeOrdinary
