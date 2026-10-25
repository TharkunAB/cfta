import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion

namespace MicroCFTA.SourcePruningEnumerationNativeOrdinary
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) ×
  EnumerationState.State Symbol Constraint))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain actual entry and scan the selected edges only for an ordinary nonterminal parent. -/
noncomputable def run (checkEmpty : Bool) (r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) : Raw × Option (Result width) :=
  let raw := ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core)
  (raw, match raw with
    | [.ok ((target, _handle, scs, parent@(.node _ _ _ _)), entered)] =>
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
        else some (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame entered before) (edgesOf parent) caller queries)
    | _ => none)

/-- Entry errors and rejected or unsupported entry rows remain exact at every fixed bound. -/
theorem entry_readback (checkEmpty : Bool) (r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run checkEmpty r n p h k uv edgesOf caller before queries).1 =
      ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) := rfl

/-- A terminal parent does not enter the ordinary shallow alternative scan. -/
theorem terminal (checkEmpty : Bool) (r n p h k uv target handle : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (entered : EnumerationState.State Symbol Constraint) (queries : Queries)
    (observed : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
      [.ok ((target, handle, scs, .node entry edges depth free), entered)])
    (blocked : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true) :
    run checkEmpty r n p h k uv edgesOf caller before queries =
      ([.ok ((target, handle, scs, .node entry edges depth free), entered)], none) := by
  simp only [run, observed, blocked, ite_true]

/-- Numeric branch admission applies only at the actual ordinary entry endpoint. -/
def Ranges (checkEmpty : Bool) (uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  ∀ fuel target handle scs entry edges depth free entered,
    ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap fuel uv before.core) =
      [.ok ((target, handle, scs, .node entry edges depth free), entered)] →
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false →
    SourcePruningEnumerationNativeBranchCompletion.Ranges checkEmpty target scs
      (EnumerationExpandableIndex.frame entered before) (edgesOf (.node entry edges depth free)) caller queries

/-- Actual ready entry retains Caller receipts and fragment history for each processed alternative. -/
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
        result = .complete processed afterCaller saved) := by
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
    branches, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory, shape, supported⟩ :=
    SourcePruningEnumerationNativeBranchCompletion.complete_with_history formulas solver inventory caller entered checkEmpty
      uv handle scs parentEntry storedEdges (edgesOf (.node parentEntry storedEdges depth free)) depth free roots memos
      initial enteredReady enteredStored decoded enteredRealized selected enteredPaths enteredCounts enteredFlags
      (retained scs pending) branchRanges
  refine ⟨e + r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    ?_, stable, sameFlags, sameWaiting, post, querySame, admitted, ?_, receiptPosts, ?_, shape, supported⟩
  · intro er en P H ek largeP largeH
    have observed := entryRun (r + er)
    have scanned := branches (e + er) en P H ek largeP largeH
    have common : SourcePruningEnumerationNativeBranches.run checkEmpty (e + r + er) (n + en) P H (k + ek)
        uv scs entered (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query = result := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using scanned
    simp only [Nat.add_assoc] at observed common ⊢
    simp only [run, observed, nonterminal, Bool.false_eq_true, ite_false, frame, common]
  · intro history incoming
    exact pendingHistory (EnumerationReferences.pending_read before.core entered.core stable history)
      (EnumerationReferences.incoming_read uv before.core entered.core stable incoming)
  · intro receipt member
    exact SourcePruningEnumerationNativeBranchCompletion.fragmentHistory_transport before.core entered.core
      (fun level frontier stratified =>
        ⟨level, EnumerationOrder.stratified_read before.core entered.core level frontier stable stratified⟩)
      receipt (fragmentHistory receipt member)

/-- Actual ready entry retains the full prefix Caller receipt for each processed alternative. -/
theorem complete_with_posts
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
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) := by
  obtain ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    observed, stable, flagsSame, waitingSame, post, querySame, admitted, pendingHistory,
    receiptPosts, _fragmentHistory, shape, supported⟩ :=
    complete_with_history formulas solver inventory caller before checkEmpty uv handle scs parentEntry
      storedEdges depth free edgesOf roots memos initial ready stored decoded realized selected paths counts flags pending nonterminal ranges
  exact ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    observed, stable, flagsSame, waitingSame, post, querySame, admitted, pendingHistory, receiptPosts, shape, supported⟩

/-- Actual ready entry derives one admitted ordinary scan with the selected native edge callback. -/
theorem complete
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
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) := by
  obtain ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    run, render, sameFlags, sameWaiting, post, query, admitted, history, _posts, shape, supported⟩ :=
    complete_with_posts formulas solver inventory caller before checkEmpty uv handle scs parentEntry
      storedEdges depth free edgesOf roots memos initial ready stored decoded realized selected paths counts flags pending nonterminal ranges
  exact ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    run, render, sameFlags, sameWaiting, post, query, admitted, history, shape, supported⟩

/-- Actual selection derives ready entry and pending-reference validity for every processed alternative. -/
theorem selected_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (preference : List Nat → Option Nat) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (history : EnumerationReferences.PendingReferences before.core)
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
      (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Pending receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) := by
  have ready := SourcePruningEnumerationSelection.ready caller.checked.native.machine.heap before preference uv
    safe roots paths counts flags selection
  have incoming := SourcePruningEnumerationSelection.incoming caller.checked.native.machine.heap before preference uv
    safe roots paths counts flags selection
  have pending := EnumerationReferences.pending_inputs before.core history uv (some handle) scs stored
  obtain ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    observed, stable, flagsSame, waitingSame, post, querySame, admitted, pendingHistory, shape, supported⟩ :=
    complete formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free
      edgesOf roots memos initial ready stored decoded realized selected paths counts flags pending nonterminal ranges
  exact ⟨r, n, p, h, k, entered, processed, afterCaller, saved, final, next, result,
    observed, stable, flagsSame, waitingSame, post, querySame, admitted, pendingHistory history incoming, shape, supported⟩

end MicroCFTA.SourcePruningEnumerationNativeOrdinary
