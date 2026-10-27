import MicroCFTA.SourceFlatPruningNativeOrdinary
import MicroCFTA.SourceFlatPruningNativeBranchCompletion
import MicroCFTA.SourcePruningEnumerationNativeOrdinary

/-!
# Original ordinary completion with actual flat entry

The old entry and branch packets supply the same caller and full memos.
The flat wrapper reads its actual entry once before the ordered scan.
-/

namespace MicroCFTA.SourceFlatPruningNativeOrdinaryCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeOrdinary (Ranges run)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "FlatRaw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) ×
  EnumerationFlatState.State Symbol Constraint))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the complete old history packet and append its actual flat ordinary run. -/
theorem complete_with_history
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
    (ranges : Ranges checkEmpty uv edgesOf caller before memos.query) :
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
      (∀ (flat : EnumerationFlatCached.Cached Symbol Constraint),
        EnumerationFlatCached.Related flat before →
        ∀ extraNative P H, p ≤ P → h ≤ H →
          ∃ flatResult,
            SourceFlatPruningNativeOrdinary.run checkEmpty (n + extraNative) P H
              uv edgesOf caller flat memos.query = flatResult ∧
            SourceFlatPruningNativeOrdinary.ResultRelated flatResult
              ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)], some result)) := by
  obtain ⟨e, value, entered, entryRun, lookup, _available, _closed, _counter, _values,
    sameFlags, sameWaiting, enteredStored, enteredReady, _protected, enteredPaths, enteredRealized,
    enteredCounts, enteredFlags, _bounded, retained, stable⟩ :=
    SourcePruningEnumerationSelectedEntry.complete caller.checked.native.machine.heap before uv handle scs roots
      ready stored realized paths counts flags
  have same : value = .node parentEntry storedEdges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have frame : EnumerationExpandableIndex.frame entered.core before = entered := by
    cases entered with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact sameFlags.symm
        · exact sameWaiting.symm
  have branchRanges : SourcePruningEnumerationNativeBranchCompletion.Ranges checkEmpty uv scs entered
      (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query := by
    rw [← frame]
    exact ranges e uv handle scs parentEntry storedEdges depth free entered.core
      (by simpa only [Nat.add_zero] using entryRun 0) nonterminal
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    branches, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory, shape, supported, flatBranches⟩ :=
    SourceFlatPruningNativeBranchCompletion.complete_with_history formulas solver inventory caller entered checkEmpty
      uv handle scs parentEntry storedEdges (edgesOf (.node parentEntry storedEdges depth free)) depth free roots memos
      initial enteredReady enteredStored decoded enteredRealized selected enteredPaths enteredCounts enteredFlags
      (retained scs pending) branchRanges
  refine ⟨e + r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    ?_, stable, sameFlags, sameWaiting, post, querySame, admitted, ?_, receiptPosts, ?_, shape, supported, ?_⟩
  · intro er en P H ek largeP largeH
    have observed := entryRun (r + er)
    have scanned := branches (e + er) en P H ek largeP largeH
    have common : SourcePruningEnumerationNativeBranches.run checkEmpty (e + r + er) (n + en) P H (k + ek)
        uv scs entered (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query = result := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using scanned
    simp only [Nat.add_assoc] at observed common ⊢
    simp only [SourcePruningEnumerationNativeOrdinary.run, observed, nonterminal,
      Bool.false_eq_true, ite_false, frame, common]
  · intro history incoming
    exact pendingHistory (EnumerationReferences.pending_read before.core entered.core stable history)
      (EnumerationReferences.incoming_read uv before.core entered.core stable incoming)
  · intro receipt member
    exact SourcePruningEnumerationNativeBranchCompletion.fragmentHistory_transport before.core entered.core
      (Nat.le_of_eq stable.counter.symm)
      (fun level frontier stratified =>
        ⟨level, EnumerationOrder.stratified_read before.core entered.core level frontier stable stratified⟩)
      receipt (fragmentHistory receipt member)

  · intro flat related extraNative P H enoughP enoughH
    obtain ⟨read, flatEntry, enteredCores⟩ :=
      SourceFlatPruningEntry.enter_replays caller.checked.native.machine.heap e uv
        flat.core before.core (uv, handle, scs, .node parentEntry storedEdges depth free) entered.core
        related.core (by simpa only [Nat.add_zero] using entryRun 0)
    let enteredFlat := EnumerationFlatCached.frame read flat
    have enteredRelated : EnumerationFlatCached.Related enteredFlat entered := by
      rw [← frame]
      exact EnumerationFlatCached.frame_related related enteredCores
    obtain ⟨flatBranchesResult, branchesRun, branchesRelated⟩ :=
      flatBranches enteredFlat enteredRelated extraNative P H enoughP enoughH
    let flatResult : FlatRaw × Option (SourceFlatPruningNativeBranches.Result width) :=
      ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), read)], some flatBranchesResult)
    refine ⟨flatResult, ?_, ?_⟩
    · simp only [SourceFlatPruningNativeOrdinary.run, flatEntry, nonterminal,
        Bool.false_eq_true, ite_false]
      change (([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), read)] : FlatRaw),
        some (SourceFlatPruningNativeBranches.run checkEmpty (n + extraNative) P H
          uv scs enteredFlat (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query)) = flatResult
      rw [branchesRun]
    · exact ⟨.cons (.ok _ enteredCores) .nil, branchesRelated⟩

end MicroCFTA.SourceFlatPruningNativeOrdinaryCompletion
