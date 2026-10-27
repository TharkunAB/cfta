import MicroCFTA.SourcePruningEnumerationNativeBranchBoundedResources
import MicroCFTA.SourceFlatPruningCapturedResources
import MicroCFTA.SourceFlatPruningNativeBranches

/-!
# Actual flat heads from original resource admission

Each alternative uses the same captured enumeration cache.
Its actual returned caller and queries pass to the next alternative.
The original projected buckets determine every reserved mixed query step.
Each processed receipt retains bounds for its own exact selected-edge prefix.
-/
namespace MicroCFTA.SourceFlatPruningNativeHeadResources
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
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {bits : Nat}

open SourcePruningEnumerationNativeBranchCompletion (CacheValid Admitted Pending FragmentHistory edgeCost HeadCacheBounds observed_head_cache_bounds)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original resources derive one actual native alternative and its complete receipt. -/
theorem head_complete_resources
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
        afterCaller.checked.native.machine.heap ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ en P H, p ≤ P → h ≤ H →
          ∃ flatReceipt,
            SourceFlatPruningCapturedEdge.run checkEmpty (n + en) P H uv scs edge
              caller flat memos.query = some flatReceipt ∧
            SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        have noCost : edgeCost scs before.core.counter edge = 0 := by
          simp only [edgeCost, allowed, ↓reduceIte, projected]
        refine ⟨0, 0, 0, 0, 0, .unhandled, caller, memos.query, memos, inventory,
          ?_, Post.refl initial, rfl, trivial, (fun _ _ => trivial), trivial, .inr ⟨rfl, allowed, rfl⟩,
          ?_, ?_, ?_⟩
        · intro er en P H ek _largeP _largeH
          rw [SourcePruningEnumerationCapturedEdge.run,
            SourcePruningEnumerationSelectedEdge.unsupported checkEmpty _ _ _ _ _ scs edge caller before memos.query
              allowed projected]
        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using fits
        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known
        · intro flat _related en P H _largeP _largeH
          refine ⟨.unhandled, ?_, trivial⟩
          simp only [SourceFlatPruningCapturedEdge.run, SourceFlatPruningSelectedEdge.run,
            SourceFlatPruningCachedOwn.prepare, allowed, ↓reduceIte, projected]
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
          afterFlags, _origin, _retained, _protects, pendingHistory, shape, returnedFits, returnedKnown, flatRunning⟩ :=
          SourceFlatPruningCapturedResources.complete_with_history_resources seed formulas solver inventory caller before checkEmpty
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
          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            ⟨valid, safe, bounded, written, ancestry, root⟩, pendingHistory, ⟨growth, fragmentPending, ordered⟩,
            .inl rfl, headFits, headKnown, ?_⟩
          intro flat related en P H largeP largeH
          obtain ⟨flatReceipt, actual, compared, _correct⟩ := flatRunning flat related en P H largeP largeH
          exact ⟨flatReceipt, actual, compared⟩
        · subst result
          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            valid, pendingHistory, trivial, .inl rfl, headFits, headKnown, ?_⟩
          intro flat related en P H largeP largeH
          obtain ⟨flatReceipt, actual, compared, _correct⟩ := flatRunning flat related en P H largeP largeH
          exact ⟨flatReceipt, actual, compared⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    have noCost : edgeCost scs before.core.counter edge = 0 := by
      simp only [edgeCost, rejected, Bool.false_eq_true, ↓reduceIte]
    refine ⟨0, 0, 0, 0, 0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, ⟨roots, paths, ready.safe.1, realized, counts, flags⟩,
      (fun history _ => history), trivial, .inl rfl, ?_, ?_, ?_⟩
    · intro er en P H ek _largeP _largeH
      rw [SourcePruningEnumerationCapturedEdge.run,
        SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty _ _ _ _ _ scs edge caller before memos.query rejected]
    · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using fits
    · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known
    · intro flat related en P H _largeP _largeH
      refine ⟨.rejected caller memos.query flat, ?_, rfl, rfl, related⟩
      simp only [SourceFlatPruningCapturedEdge.run, SourceFlatPruningSelectedEdge.run,
        SourceFlatPruningCachedOwn.prepare, rejected, Bool.false_eq_true, ↓reduceIte]

/-- The original head producer retains every receipt field and adds original-input cache bounds. -/
theorem head_complete_cache_bounds
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
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (arity own : Nat) (arityBound : edge.children.length ≤ arity)
    (ownBound : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
        tries.length ≤ own) :
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
        afterCaller.checked.native.machine.heap ∧
      HeadCacheBounds before scs arity own receipt ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ en P H, p ≤ P → h ≤ H →
          ∃ flatReceipt,
            SourceFlatPruningCapturedEdge.run checkEmpty (n + en) P H uv scs edge
              caller flat memos.query = some flatReceipt ∧
            SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt) := by
  obtain ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown, flatRunning⟩ :=
    head_complete_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
      paths counts flags pending fits reserved known
  refine ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown, ?_, flatRunning⟩
  have observed := running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at observed
  exact observed_head_cache_bounds checkEmpty r n p h k uv scs edge caller before memos.query
    arity own arityBound ownBound receipt observed


end MicroCFTA.SourceFlatPruningNativeHeadResources
