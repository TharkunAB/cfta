import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources

/-!
# Original resources through ordered native alternatives

Each alternative uses the same captured enumeration cache.
Its actual returned caller and queries pass to the next alternative.
The original projected buckets determine every reserved mixed query step.
Each processed receipt retains bounds for its own exact selected-edge prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeBranches (advance)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {bits : Nat}

/-- Count the original projected child cost of one actual supported alternative. -/
noncomputable def edgeCost (scs : List Suspended) (start : Nat) (edge : EdgeValue Symbol Constraint) : Nat :=
  if arityAllows edge.children.length scs then
    match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => 0
    | some (tries, _) => SourcePruningEnumerationSelectedEdge.cost edge scs start tries
  else 0

/-- Count alternatives in their original order, including duplicate entries. -/
noncomputable def cost (scs : List Suspended) (start : Nat) : List (EdgeValue Symbol Constraint) → Nat
  | [] => 0
  | edge :: rest => edgeCost scs start edge + cost scs start rest

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem head_complete_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
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
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (edgeCost scs before.core.counter edge))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (receipt : Receipt (bits + 2)) (afterCaller : Caller (bits + 2)) (saved : Queries)
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
      Fits (reservationAdvance seed (edgeCost scs before.core.counter edge)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (edgeCost scs before.core.counter edge)).1)
        afterCaller.checked.native.machine.heap := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        have noCost : edgeCost scs before.core.counter edge = 0 := by
          simp only [edgeCost, allowed, ↓reduceIte, projected]
        refine ⟨0, 0, 0, 0, 0, .unhandled, caller, memos.query, memos, inventory,
          ?_, Post.refl initial, rfl, trivial, (fun _ _ => trivial), trivial, .inr ⟨rfl, allowed, rfl⟩,
          ?_, ?_⟩
        · intro er en P H ek _largeP _largeH
          rw [SourcePruningEnumerationCapturedEdge.run,
            SourcePruningEnumerationSelectedEdge.unsupported checkEmpty _ _ _ _ _ scs edge caller before memos.query
              allowed projected]
        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using fits
        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known
    | some pair =>
        rcases pair with ⟨tries, residual⟩
        have actualCost : edgeCost scs before.core.counter edge =
            SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
          simp only [edgeCost, allowed, ↓reduceIte, projected]
        have actualReserved : Reserved bits seed
            (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
          simpa only [actualCost] using reserved
        obtain ⟨r, n, p, h, k, afterCaller, after, saved, final, next, afterRoots, result,
          stable, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
          afterFlags, _origin, _retained, _protects, pendingHistory, shape, returnedFits, returnedKnown⟩ :=
          SourcePruningEnumerationCapturedEdge.complete_with_history_resources seed formulas solver inventory caller before checkEmpty
            uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
            selected paths counts flags pending allowed tries residual projected fits actualReserved known
        have valid : CacheValid afterCaller after :=
          ⟨afterRoots, afterPaths, storage, afterRealized, afterCounts, afterFlags⟩
        have headFits : Fits (reservationAdvance seed (edgeCost scs before.core.counter edge)).2 afterCaller.checked := by
          simpa only [actualCost] using returnedFits
        have headKnown : Heap (fun guard => guard ∈
            (reservationAdvance seed (edgeCost scs before.core.counter edge)).1)
            afterCaller.checked.native.machine.heap := by
          simpa only [actualCost] using returnedKnown
        rcases shape with ⟨fragment, completed, safe, bounded, written, ancestry, root, fragmentPending, ordered⟩ |
          ⟨fragments, outer, waiting, stopped⟩
        · subst result
          exact ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            ⟨valid, safe, bounded, written, ancestry, root⟩, pendingHistory, ⟨growth, fragmentPending, ordered⟩,
            .inl rfl, headFits, headKnown⟩
        · subst result
          exact ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            valid, pendingHistory, trivial, .inl rfl, headFits, headKnown⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    have noCost : edgeCost scs before.core.counter edge = 0 := by
      simp only [edgeCost, rejected, Bool.false_eq_true, ↓reduceIte]
    refine ⟨0, 0, 0, 0, 0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, ⟨roots, paths, ready.safe.1, realized, counts, flags⟩,
      (fun history _ => history), trivial, .inl rfl, ?_, ?_⟩
    · intro er en P H ek _largeP _largeH
      rw [SourcePruningEnumerationCapturedEdge.run,
        SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty _ _ _ _ _ scs edge caller before memos.query rejected]
    · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using fits
    · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known

/-- Original resources retain all receipt histories and each exact reached prefix. -/
theorem complete_with_history_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
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
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost scs before.core.counter selectedEdges))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (processed : List (Receipt (bits + 2))) (afterCaller : Caller (bits + 2)) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result (bits + 2)),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, Pending receipt) ∧
      (∀ receipt ∈ processed,
        ∃ (reached : Caller (bits + 2)) (savedQueries : Queries) (receiptInventory : Inventory) (receiptMemos : Memos),
          advance receipt = some (reached, savedQueries) ∧
          Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
      (∀ receipt ∈ processed, FragmentHistory before.core receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      Fits (reservationAdvance seed (cost scs before.core.counter selectedEdges)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter selectedEdges)).1)
        afterCaller.checked.native.machine.heap ∧
      (∀ (index : Nat) (receipt : Receipt (bits + 2)), processed[index]? = some receipt →
        ∃ (reached : Caller (bits + 2)) (savedQueries : Queries),
          advance receipt = some (reached, savedQueries) ∧
          Fits (reservationAdvance seed (cost scs before.core.counter (selectedEdges.take (index + 1)))).2
            reached.checked ∧
          Heap (fun guard => guard ∈
            (reservationAdvance seed (cost scs before.core.counter (selectedEdges.take (index + 1)))).1)
            reached.checked.native.machine.heap) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      exact ⟨0, 0, 0, 0, 0, [], caller, memos.query, memos, inventory, .complete [] caller memos.query,
        fun _ _ _ _ _ _ _ => rfl, Post.refl initial, rfl, by simp,
        (by intro _ _ receipt member; cases member), (by intro receipt member; cases member),
        (by intro receipt member; cases member), .inl rfl, (fun _ => rfl), fits, known,
        (by intro index receipt found; cases found)⟩
  | cons edge rest ih =>
      have headReserved : Reserved bits seed (edgeCost scs before.core.counter edge) :=
        reserved.prefix (by
          change edgeCost scs before.core.counter edge ≤
            edgeCost scs before.core.counter edge + cost scs before.core.counter rest
          omega)
      obtain ⟨r, n, p, h, k, receipt, middleCaller, middleQueries, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, headPending, headHistory, shape, headFits, headKnown⟩ :=
        head_complete_resources seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free
          edge roots memos initial ready stored decoded realized (selected edge (by simp)) paths counts flags pending fits headReserved known
      rcases shape with continued | ⟨unhandled, allowed, projected⟩
      · have kept := headPost.effects.keeps
        have middleRealized : PendingRealized middleCaller.checked.native.machine.heap before.core :=
          realized_preserved _ _ before.core before.core realized (EnumerationCompressionFrame.Frame.refl _) kept
        have middleFlags := SourcePruningEnumerationNativeGrowth.flags _ _ kept before flags
        have tailReserved : Reserved bits
            (reservationAdvance seed (edgeCost scs before.core.counter edge))
            (cost scs before.core.counter rest) := reserved.after_prefix
        obtain ⟨tr, tn, tp, th, tk, processed, afterCaller, saved, final, next, tailResult,
          tailRun, tailPost, querySame, admittedTail, tailPending, tailPosts, tailHistory, tailShape, tailSupported,
          tailFits, tailKnown, tailResources⟩ :=
          ih (reservationAdvance seed (edgeCost scs before.core.counter edge))
            middleInventory middleCaller middleMemos headPost.context
            (lookupNode_keeps _ _ kept handle _ decoded) middleRealized
            (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) middleFlags headFits tailReserved headKnown
        let result : Result (bits + 2) := match (generalizing := false) tailResult with
          | .complete receipts afterCaller saved => .complete (receipt :: receipts) afterCaller saved
          | .stopped receipts current => .stopped (receipt :: receipts) current
        refine ⟨r + tr, n + tn, max p tp, max h th, k + tk, receipt :: processed,
          afterCaller, saved, final, next, result, ?_, headPost.trans tailPost, querySame, ?_, ?_, ?_, ?_, ?_, ?_,
          (by simpa only [cost, SourcePruningEnumerationIncomingReservation.advance_add] using tailFits),
          (by simpa only [cost, SourcePruningEnumerationIncomingReservation.advance_add] using tailKnown), ?_⟩
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
        · intro index current found
          cases index with
          | zero =>
              have same : receipt = current := Option.some.inj found
              subst current
              refine ⟨middleCaller, middleQueries, continued, ?_, ?_⟩
              · simpa only [List.take_succ_cons, List.take_zero, cost, Nat.add_zero] using headFits
              · simpa only [List.take_succ_cons, List.take_zero, cost, Nat.add_zero] using headKnown
          | succ index =>
              have tailFound : processed[index]? = some current := by
                simpa only [List.getElem?_cons_succ] using found
              obtain ⟨reached, savedQueries, advanced, prefixFits, prefixKnown⟩ :=
                tailResources index current tailFound
              refine ⟨reached, savedQueries, advanced, ?_, ?_⟩
              · simpa only [List.take_succ_cons, cost,
                  SourcePruningEnumerationIncomingReservation.advance_add] using prefixFits
              · simpa only [List.take_succ_cons, cost,
                  SourcePruningEnumerationIncomingReservation.advance_add] using prefixKnown
      · subst receipt
        refine ⟨r, n, p, h, k, [], middleCaller, middleQueries, middleMemos, middleInventory,
          .stopped [] (some .unhandled), ?_, headPost, headQueries, by simp,
          (by intro _ _ current member; cases member), (by intro current member; cases member),
          (by intro current member; cases member), .inr rfl, ?_, ?_, ?_, ?_⟩
        · intro er en P H ek largeP largeH
          simp only [SourcePruningEnumerationNativeBranches.run, headRun er en P H ek largeP largeH, advance]
        · intro supported
          exact (supported edge (by simp) allowed projected).elim
        · change Fits (reservationAdvance seed
            (edgeCost scs before.core.counter edge + cost scs before.core.counter rest)).2 middleCaller.checked
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          exact headFits.mono (SourcePruningEnumerationIncomingReservation.advance_profile_ge
            (reservationAdvance seed (edgeCost scs before.core.counter edge)) (cost scs before.core.counter rest))
        · change Heap (fun guard => guard ∈ (reservationAdvance seed
            (edgeCost scs before.core.counter edge + cost scs before.core.counter rest)).1)
            middleCaller.checked.native.machine.heap
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          intro key storedEdge found
          exact SourcePruningEnumerationIncomingReservation.advance_alphabet_ge
            (reservationAdvance seed (edgeCost scs before.core.counter edge)) (cost scs before.core.counter rest)
            (headKnown key storedEdge found)
        · intro index current found
          cases found

/-- The resource interface retains every original per-receipt caller postcondition. -/
theorem complete_with_posts_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
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
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost scs before.core.counter selectedEdges))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (processed : List (Receipt (bits + 2))) (afterCaller : Caller (bits + 2)) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result (bits + 2)),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, Pending receipt) ∧
      (∀ receipt ∈ processed,
        ∃ (reached : Caller (bits + 2)) (savedQueries : Queries) (receiptInventory : Inventory) (receiptMemos : Memos),
          advance receipt = some (reached, savedQueries) ∧
          Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      Fits (reservationAdvance seed (cost scs before.core.counter selectedEdges)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter selectedEdges)).1)
        afterCaller.checked.native.machine.heap := by
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    running, post, query, admitted, pendingHistory, posts, _fragmentHistory, shape, supported,
    returnedFits, returnedKnown, _indexedResources⟩ :=
    complete_with_history_resources seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry
      storedEdges selectedEdges depth free roots memos initial ready stored decoded realized selected paths counts flags pending fits reserved known
  exact ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    running, post, query, admitted, pendingHistory, posts, shape, supported, returnedFits, returnedKnown⟩

/-- Original resources derive the earlier alternatives packet at its actual final caller. -/
theorem complete_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
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
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost scs before.core.counter selectedEdges))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (processed : List (Receipt (bits + 2))) (afterCaller : Caller (bits + 2)) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result (bits + 2)),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, Pending receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      Fits (reservationAdvance seed (cost scs before.core.counter selectedEdges)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter selectedEdges)).1)
        afterCaller.checked.native.machine.heap := by
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    run, post, query, admitted, history, _posts, shape, supported, returnedFits, returnedKnown⟩ :=
    complete_with_posts_resources seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry
      storedEdges selectedEdges depth free roots memos initial ready stored decoded realized selected paths counts flags pending fits reserved known
  exact ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    run, post, query, admitted, history, shape, supported, returnedFits, returnedKnown⟩

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
