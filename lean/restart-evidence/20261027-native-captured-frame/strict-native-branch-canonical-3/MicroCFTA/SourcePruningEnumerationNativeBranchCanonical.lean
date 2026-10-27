import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
import MicroCFTA.SourcePruningEnumerationCapturedEdgeCanonical

/-!
# Canonical storage in actual native alternative receipts

Each alternative uses the same captured enumeration cache.
The actual prefix Post supplies the next native context and its full memos.
Only a completed receipt is certified here.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationValidity
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNativeBranches (advance)
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
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
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A stopped scan retains every receipt before its exact stopping observation. -/
def processedReceipts : Result width → List (Receipt width)
  | .complete processed _ _ | .stopped processed _ => processed

/-- Actual prefix receipts supply the contexts used to certify completed branch caches. -/
theorem observed_canonical
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (canonical : Canonical before.core)
    {r n p h k : Nat} {result : Result width}
    (observed : SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k
      uv scs before selectedEdges caller memos.query = result)
    (receiptPosts : ∀ receipt ∈ processedReceipts result,
      ∃ (reached : Caller width) (saved : Queries) (next : Inventory) (final : Memos),
        SourcePruningEnumerationNativeBranches.advance receipt = some (reached, saved) ∧
        Post formulas solver next caller reached final ∧ final.query = saved) :
    ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      .complete fragment reached saved after ∈ processedReceipts result → Canonical after.core := by
  subst result
  have scan : ∀ (remaining : List (EdgeValue Symbol Constraint))
      (currentInventory : Inventory) (currentCaller : Caller width) (currentMemos : Memos),
      Post formulas solver currentInventory caller currentCaller currentMemos →
      (∀ edge ∈ remaining, edge ∈ storedEdges) →
      (∀ receipt ∈ processedReceipts (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k
          uv scs before remaining currentCaller currentMemos.query),
        ∃ (reached : Caller width) (saved : Queries) (next : Inventory) (final : Memos),
          SourcePruningEnumerationNativeBranches.advance receipt = some (reached, saved) ∧
          Post formulas solver next caller reached final ∧ final.query = saved) →
      ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
        .complete fragment reached saved after ∈ processedReceipts
          (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k
            uv scs before remaining currentCaller currentMemos.query) → Canonical after.core := by
    intro remaining
    induction remaining with
    | nil =>
        intro currentInventory currentCaller currentMemos _currentPost _selected _posts
          fragment reached saved after member
        cases member
    | cons edge rest ih =>
        intro currentInventory currentCaller currentMemos currentPost selectedCurrent posts
        cases head : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k uv scs edge
            currentCaller before currentMemos.query with
        | none =>
            simp only [SourcePruningEnumerationNativeBranches.run, head, processedReceipts]
            intro fragment reached saved after member
            cases member
        | some receipt =>
            cases continued : SourcePruningEnumerationNativeBranches.advance receipt with
            | none =>
                simp only [SourcePruningEnumerationNativeBranches.run, head, continued, processedReceipts]
                intro fragment reached saved after member
                cases member
            | some endpoint =>
                rcases endpoint with ⟨middleCaller, middleQueries⟩
                have processedRun : processedReceipts (SourcePruningEnumerationNativeBranches.run
                    checkEmpty r n p h k uv scs before (edge :: rest) currentCaller currentMemos.query) =
                    receipt :: processedReceipts (SourcePruningEnumerationNativeBranches.run
                      checkEmpty r n p h k uv scs before rest middleCaller middleQueries) := by
                  simp only [SourcePruningEnumerationNativeBranches.run, head, continued]
                  cases SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k
                    uv scs before rest middleCaller middleQueries <;> rfl
                rw [processedRun] at posts ⊢
                obtain ⟨headCaller, headQueries, headInventory, headMemos,
                    headAdvanced, headPost, headQuery⟩ := posts receipt (by simp)
                have endpoints : (headCaller, headQueries) = (middleCaller, middleQueries) :=
                  Option.some.inj (headAdvanced.symm.trans continued)
                obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
                rw [callerSame] at headPost
                rw [querySame] at headQuery
                have tailPosts : ∀ current ∈ processedReceipts
                    (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k
                      uv scs before rest middleCaller headMemos.query),
                    ∃ (reached : Caller width) (saved : Queries) (next : Inventory) (final : Memos),
                      SourcePruningEnumerationNativeBranches.advance current = some (reached, saved) ∧
                      Post formulas solver next caller reached final ∧ final.query = saved := by
                  rw [headQuery]
                  intro current member
                  exact posts current (List.mem_cons_of_mem _ member)
                have tailCanonical := ih headInventory middleCaller headMemos headPost
                  (fun chosen member => selectedCurrent chosen (List.mem_cons_of_mem _ member)) tailPosts
                rw [headQuery] at tailCanonical
                intro fragment reached saved after member
                rcases List.mem_cons.mp member with same | member
                · have completed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k uv scs edge
                      currentCaller before currentMemos.query = some (.complete fragment reached saved after) :=
                    head.trans (congrArg some same.symm)
                  by_cases allowed : arityAllows edge.children.length scs = true
                  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
                    | none =>
                        rw [SourcePruningEnumerationCapturedEdge.run,
                          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty r n p h k scs edge
                            currentCaller before currentMemos.query allowed projected] at completed
                        cases completed
                    | some pair =>
                        rcases pair with ⟨tries, residual⟩
                        have kept := currentPost.effects.keeps
                        exact SourcePruningEnumerationCapturedEdge.complete_canonical formulas solver
                          currentInventory currentCaller before checkEmpty uv handle scs parentEntry storedEdges depth
                          free edge roots currentMemos currentPost.context ready stored
                          (lookupNode_keeps _ _ kept handle _ decoded)
                          (realized_preserved _ _ before.core before.core realized
                            (EnumerationCompressionFrame.Frame.refl _) kept)
                          (selectedCurrent edge (by simp)) paths counts
                          (SourcePruningEnumerationNativeGrowth.flags _ _ kept before flags)
                          pending allowed tries residual projected canonical completed
                  · have rejected : arityAllows edge.children.length scs = false := by
                      cases value : arityAllows edge.children.length scs with
                      | false => rfl
                      | true => exact (allowed value).elim
                    rw [SourcePruningEnumerationCapturedEdge.run,
                      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge
                        currentCaller before currentMemos.query rejected] at completed
                    cases completed
                · exact tailCanonical fragment reached saved after member
  exact scan selectedEdges inventory caller memos (Post.refl initial) selected receiptPosts

/-- The original stable producer retains every result and adds canonical completed caches. -/
theorem complete_with_history_canonical
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (ranges : Ranges checkEmpty uv scs before selectedEdges caller memos.query)
    (canonical : Canonical before.core) :
    ∃ (r n p h k : Nat) (processed : List (Receipt width)) (afterCaller : Caller width) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result width),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, Pending receipt) ∧
      (∀ receipt ∈ processed,
        ∃ (reached : Caller width) (savedQueries : Queries) (receiptInventory : Inventory) (receiptMemos : Memos),
          advance receipt = some (reached, savedQueries) ∧
          Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
      (∀ receipt ∈ processed, FragmentHistory before.core receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      (∀ (fragment : Fragment) (reached : Caller width) (queries : Queries) (after : Cached),
        .complete fragment reached queries after ∈ processed → Canonical after.core) := by
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    stable, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory, shape, supported⟩ :=
    complete_with_history formulas solver inventory caller before checkEmpty uv handle scs parentEntry
      storedEdges selectedEdges depth free roots memos initial ready stored decoded realized selected paths counts
      flags pending ranges
  have receiptView : processedReceipts result = processed := by
    rcases shape with completed | stopped
    · rw [completed]
      rfl
    · rw [stopped]
      rfl
  have actual : SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k uv scs before
      selectedEdges caller memos.query = result := by
    simpa only [Nat.add_zero] using stable 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  have canonicalResults := observed_canonical formulas solver inventory caller before checkEmpty uv handle scs
    parentEntry storedEdges selectedEdges depth free roots memos initial ready stored decoded realized selected
    paths counts flags pending canonical actual (by simpa only [receiptView] using receiptPosts)
  refine ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    stable, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory, shape, supported, ?_⟩
  simpa only [receiptView] using canonicalResults

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
