import MicroCFTA.SourceFlatPruningNativeBranches
import MicroCFTA.SourceFlatPruningCapturedCompletion
import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion

/-!
# Ordered native branch completion with direct-parent forests

Every sibling uses the same captured cache. Each completed head supplies its
actual native caller and saved queries to the suffix. The proof keeps the full
original caller, memo, reference and fragment-history receipts.
-/

namespace MicroCFTA.SourceFlatPruningNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeBranches (advance)
open SourcePruningEnumerationNativeBranchCompletion (CacheValid Admitted Pending FragmentHistory Ranges)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "FlatReceipt" => SourceFlatPruningSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
variable {width : Nat}

private theorem advance_some
    (left : FlatReceipt width) (right : Receipt width)
    (related : SourceFlatPruningSelectedEdge.ResultRelated left right)
    (caller : Caller width) (queries : Queries)
    (continued : advance right = some (caller, queries)) :
    SourceFlatPruningNativeBranches.advance left = some (caller, queries) := by
  cases right with
  | unhandled => cases continued
  | rejected oldCaller oldQueries oldAfter =>
      cases left with
      | unhandled | complete _ _ _ _ | stopped _ _ _ => cases related
      | rejected reached saved recovered =>
          obtain ⟨rfl, rfl, _caches⟩ := related
          exact continued
  | complete fragment oldCaller oldQueries oldAfter =>
      cases left with
      | unhandled | rejected _ _ _ | stopped _ _ _ => cases related
      | complete flatFragment reached saved recovered =>
          obtain ⟨_fragmentSame, rfl, rfl, _caches⟩ := related
          exact continued
  | stopped oldFragments oldObservation oldCandidate =>
      obtain ⟨oldOutcome, oldCaller, oldQueries, oldOuter, oldWaiting⟩ := oldObservation
      cases oldOutcome with
      | error fault => cases continued
      | ok oldReturned =>
          cases oldReturned with
          | none => cases continued
          | some oldRows =>
              cases oldRows with
              | cons row rows => cases continued
              | nil =>
                  cases oldCandidate with
                  | none => cases continued
                  | some oldAfter =>
                      cases left with
                      | unhandled | rejected _ _ _ | complete _ _ _ _ => cases related
                      | stopped flatFragments observation candidate =>
                          obtain ⟨outcome, reached, saved, outer, waiting⟩ := observation
                          obtain ⟨_fragmentsSame,
                            ⟨callerSame, queriesSame, _outerRelated, _waitingSame, rowsRelated⟩,
                            cacheRelated⟩ := related
                          cases candidate with
                          | none => cases cacheRelated
                          | some recovered =>
                              cases outcome with
                              | error fault =>
                                  cases fault with
                                  | inl prefixFault => cases rowsRelated
                                  | inr rest => cases rest <;> cases rowsRelated
                              | ok returned =>
                                  cases returned with
                                  | none => cases rowsRelated
                                  | some flatRows =>
                                      cases rowsRelated
                                      dsimp only at callerSame queriesSame
                                      subst reached saved
                                      exact continued

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem head_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core) (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query) :
    ∃ (r n p h k : Nat) (receipt : Receipt width) (afterCaller : Caller width) (saved : Queries)
      (final : Memos) (next : Inventory),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧ Admitted uv receipt ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        Pending receipt) ∧
      FragmentHistory before.core receipt ∧
      (advance receipt = some (afterCaller, saved) ∨
        receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ en P H, p ≤ P → h ≤ H →
          ∃ flatReceipt,
            SourceFlatPruningCapturedEdge.run checkEmpty (n + en) P H uv scs edge
              caller flat memos.query = some flatReceipt ∧
            SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        refine ⟨0, 0, 0, 0, 0, .unhandled, caller, memos.query, memos, inventory,
          ?_, Post.refl initial, rfl, trivial, (fun _ _ => trivial), trivial, .inr ⟨rfl, allowed, rfl⟩, ?_⟩
        · intro er en P H ek _largeP _largeH
          rw [SourcePruningEnumerationCapturedEdge.run,
            SourcePruningEnumerationSelectedEdge.unsupported checkEmpty _ _ _ _ _ scs edge caller before memos.query
              allowed projected]
        · intro flat _related en P H _largeP _largeH
          refine ⟨.unhandled, ?_, trivial⟩
          simp only [SourceFlatPruningCapturedEdge.run, SourceFlatPruningSelectedEdge.run,
            SourceFlatPruningCachedOwn.prepare, allowed, ↓reduceIte, projected]
    | some pair =>
        rcases pair with ⟨tries, residual⟩
        obtain ⟨r, n, p, h, k, afterCaller, after, saved, final, next, afterRoots, result,
          ⟨stable, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
            afterFlags, _origin, _retained, _protects, pendingHistory, shape⟩, flatRunning⟩ :=
          SourceFlatPruningCapturedCompletion.complete_with_history formulas solver inventory caller before checkEmpty
            uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
            selected paths counts flags pending allowed tries residual projected ranges
        have valid : CacheValid afterCaller after :=
          ⟨afterRoots, afterPaths, storage, afterRealized, afterCounts, afterFlags⟩
        rcases shape with ⟨fragment, completed, safe, bounded, written, ancestry, root, fragmentPending, ordered⟩ |
          ⟨fragments, outer, waiting, stopped⟩
        · subst result
          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            ⟨valid, safe, bounded, written, ancestry, root⟩, pendingHistory,
            ⟨growth, fragmentPending, ordered⟩, .inl rfl, ?_⟩
          intro flat related en P H largeP largeH
          obtain ⟨flatReceipt, actual, compared, _correct⟩ := flatRunning flat related en P H largeP largeH
          exact ⟨flatReceipt, actual, compared⟩
        · subst result
          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            valid, pendingHistory, trivial, .inl rfl, ?_⟩
          intro flat related en P H largeP largeH
          obtain ⟨flatReceipt, actual, compared, _correct⟩ := flatRunning flat related en P H largeP largeH
          exact ⟨flatReceipt, actual, compared⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    refine ⟨0, 0, 0, 0, 0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, ⟨roots, paths, ready.safe.1, realized, counts, flags⟩,
      (fun history _ => history), trivial, .inl rfl, ?_⟩
    · intro er en P H ek _largeP _largeH
      rw [SourcePruningEnumerationCapturedEdge.run,
        SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty _ _ _ _ _ scs edge caller before memos.query rejected]
    · intro flat related en P H _largeP _largeH
      refine ⟨.rejected caller memos.query flat, ?_, rfl, rfl, related⟩
      simp only [SourceFlatPruningCapturedEdge.run, SourceFlatPruningSelectedEdge.run,
        SourceFlatPruningCachedOwn.prepare, rejected, Bool.false_eq_true, ↓reduceIte]

/-- Preserve every original branch receipt and append the actual flat alternative scan. -/
theorem complete_with_history
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
    (ranges : Ranges checkEmpty uv scs before selectedEdges caller memos.query) :
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
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ en P H, p ≤ P → h ≤ H →
          ∃ flatResult,
            SourceFlatPruningNativeBranches.run checkEmpty (n + en) P H uv scs flat
              selectedEdges caller memos.query = flatResult ∧
            SourceFlatPruningNativeBranches.ResultRelated flatResult result) := by
  induction selectedEdges generalizing inventory caller memos with
  | nil =>
      refine ⟨0, 0, 0, 0, 0, [], caller, memos.query, memos, inventory, .complete [] caller memos.query,
        fun _ _ _ _ _ _ _ => rfl, Post.refl initial, rfl, by simp,
        (by intro _ _ receipt member; cases member), (by intro receipt member; cases member),
        (by intro receipt member; cases member), .inl rfl, fun _ => rfl, ?_⟩
      intro flat _related en P H _largeP _largeH
      exact ⟨.complete [] caller memos.query, rfl, .nil, rfl, rfl⟩
  | cons edge rest ih =>
      obtain ⟨r, n, p, h, k, receipt, middleCaller, middleQueries, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, headPending, headHistory, shape, headFlat⟩ :=
        head_complete formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free
          edge roots memos initial ready stored decoded realized (selected edge (by simp)) paths counts flags pending ranges.1
      rcases shape with continued | ⟨unhandled, allowed, projected⟩
      · have kept := headPost.effects.keeps
        have middleRealized : PendingRealized middleCaller.checked.native.machine.heap before.core :=
          realized_preserved _ _ before.core before.core realized (EnumerationCompressionFrame.Frame.refl _) kept
        have middleFlags := SourcePruningEnumerationNativeGrowth.flags _ _ kept before flags
        have tailRanges : Ranges checkEmpty uv scs before rest middleCaller middleMemos.query := by
          rw [headQueries]
          apply ranges.2 r n p h k receipt middleCaller middleQueries
          · simpa only [Nat.add_zero] using headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
          · exact continued
        obtain ⟨tr, tn, tp, th, tk, processed, afterCaller, saved, final, next, tailResult,
          tailRun, tailPost, querySame, admittedTail, tailPending, tailPosts, tailHistory, tailShape,
          tailSupported, tailFlat⟩ :=
          ih middleInventory middleCaller middleMemos headPost.context
            (lookupNode_keeps _ _ kept handle _ decoded) middleRealized
            (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) middleFlags tailRanges
        let result : Result width := match (generalizing := false) tailResult with
          | .complete receipts afterCaller saved => .complete (receipt :: receipts) afterCaller saved
          | .stopped receipts current => .stopped (receipt :: receipts) current
        refine ⟨r + tr, n + tn, max p tp, max h th, k + tk, receipt :: processed,
          afterCaller, saved, final, next, result, ?_, headPost.trans tailPost, querySame,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro er en P H ek largeP largeH
          have first := headRun (tr + er) (tn + en) P H (tk + ek)
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
          have last := tailRun (r + er) (n + en) P H (k + ek)
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have later : SourcePruningEnumerationNativeBranches.run checkEmpty (r + tr + er) (n + tn + en) P H
              (k + tk + ek) uv scs before rest middleCaller middleMemos.query = tailResult := by
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using last
          rw [headQueries] at later
          simp only [Nat.add_assoc] at later
          simp only [SourcePruningEnumerationNativeBranches.run, Nat.add_assoc, first, continued, later]
          rfl
        · intro current member
          rcases List.mem_cons.mp member with same | member
          · simpa only [same] using admitted
          · exact admittedTail current member
        · intro history incoming current member
          rcases List.mem_cons.mp member with same | member
          · simpa only [same] using headPending history incoming
          · exact tailPending history incoming current member
        · intro current member
          rcases List.mem_cons.mp member with same | member
          · subst current
            exact ⟨middleCaller, middleQueries, middleInventory, middleMemos, continued, headPost, headQueries⟩
          · obtain ⟨reached, savedQueries, receiptInventory, receiptMemos, reachedRun, receiptPost, receiptQueries⟩ :=
              tailPosts current member
            exact ⟨reached, savedQueries, receiptInventory, receiptMemos, reachedRun, headPost.trans receiptPost, receiptQueries⟩
        · intro current member
          rcases List.mem_cons.mp member with same | member
          · simpa only [same] using headHistory
          · exact tailHistory current member
        · rcases tailShape with completed | stopped
          · exact .inl (by simp only [result, completed])
          · exact .inr (by simp only [result, stopped])
        · intro supported
          have finished := tailSupported (fun chosen member fits =>
            supported chosen (List.mem_cons_of_mem _ member) fits)
          simp only [result, finished]
        · intro flat related en P H largeP largeH
          have headP := Nat.le_trans (Nat.le_max_left p tp) largeP
          have headH := Nat.le_trans (Nat.le_max_left h th) largeH
          have tailP := Nat.le_trans (Nat.le_max_right p tp) largeP
          have tailH := Nat.le_trans (Nat.le_max_right h th) largeH
          obtain ⟨flatReceipt, flatHead, comparedHead⟩ :=
            headFlat flat related (tn + en) P H headP headH
          have actualHead : SourceFlatPruningCapturedEdge.run checkEmpty (n + tn + en) P H
              uv scs edge caller flat memos.query = some flatReceipt := by
            simpa only [Nat.add_assoc] using flatHead
          have continuedFlat := advance_some flatReceipt receipt comparedHead middleCaller middleQueries continued
          obtain ⟨flatTail, flatSuffix, comparedTail⟩ :=
            tailFlat flat related (n + en) P H tailP tailH
          have actualTail : SourceFlatPruningNativeBranches.run checkEmpty (n + tn + en) P H
              uv scs flat rest middleCaller middleQueries = flatTail := by
            rw [← headQueries]
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using flatSuffix
          let flatResult : SourceFlatPruningNativeBranches.Result width :=
            match flatTail with
            | .complete receipts reached saved => .complete (flatReceipt :: receipts) reached saved
            | .stopped receipts current => .stopped (flatReceipt :: receipts) current
          refine ⟨flatResult, ?_, ?_⟩
          · simp only [SourceFlatPruningNativeBranches.run, actualHead, continuedFlat, actualTail, flatResult]
          · cases flatTail <;> cases tailResult <;>
              simp only [SourceFlatPruningNativeBranches.ResultRelated] at comparedTail <;> try contradiction
            case complete.complete flatProcessed flatCaller flatQueries oldProcessed oldCaller oldQueries =>
              obtain ⟨receipts, callerSame, queriesSame⟩ := comparedTail
              exact ⟨.cons comparedHead receipts, callerSame, queriesSame⟩
            case stopped.stopped flatProcessed flatCurrent oldProcessed oldCurrent =>
              obtain ⟨receipts, current⟩ := comparedTail
              exact ⟨.cons comparedHead receipts, current⟩
      · subst receipt
        refine ⟨r, n, p, h, k, [], middleCaller, middleQueries, middleMemos, middleInventory,
          .stopped [] (some .unhandled), ?_, headPost, headQueries, by simp,
          (by intro _ _ current member; cases member), (by intro current member; cases member),
          (by intro current member; cases member), .inr rfl, ?_, ?_⟩
        · intro er en P H ek largeP largeH
          simp only [SourcePruningEnumerationNativeBranches.run, headRun er en P H ek largeP largeH, advance]
        · intro supported
          exact (supported edge (by simp) allowed projected).elim
        · intro flat related en P H largeP largeH
          obtain ⟨flatReceipt, actualHead, compared⟩ := headFlat flat related en P H largeP largeH
          have flatUnhandled : flatReceipt = .unhandled := by
            cases flatReceipt <;> simp only [SourceFlatPruningSelectedEdge.ResultRelated] at compared <;>
              try contradiction
            rfl
          subst flatReceipt
          refine ⟨.stopped [] (some .unhandled), ?_, .nil, trivial⟩
          simp only [SourceFlatPruningNativeBranches.run, actualHead, SourceFlatPruningNativeBranches.advance]

end MicroCFTA.SourceFlatPruningNativeBranchCompletion
