import MicroCFTA.SourcePruningEnumerationSharedCapturedPreparedResources
import MicroCFTA.SourcePruningEnumerationSharedNativeBranchBoundedResources

/-!
# Actual shared heads over a separate prepared parent

The stored target handle remains unchanged. The available closed prepared
parent supplies the selected row. The actual shared head retains its full
receipt, native caller, global memos and original cache bounds.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (advance)
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationSharedIncomingReservation.advance
variable {bits : Nat}

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A current prepared parent derives the actual shared head and its complete receipt. -/
theorem head_complete_resources_prepared
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
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = [])
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
        SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
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
          rw [SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run,
            SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.unsupported checkEmpty _ _ _ _ _ scs edge caller before memos.query
              allowed projected]
        · simpa only [noCost, SourcePruningEnumerationSharedIncomingReservation.advance] using fits
        · simpa only [noCost, SourcePruningEnumerationSharedIncomingReservation.advance] using known
    | some pair =>
        rcases pair with ⟨tries, residual⟩
        have actualCost : edgeCost scs before.core.counter edge =
            SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries := by
          simp only [edgeCost, allowed, ↓reduceIte, projected]
        have actualReserved : Reserved bits seed
            (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries) := by
          simpa only [actualCost] using reserved
        obtain ⟨r, n, p, h, k, afterCaller, after, saved, final, next, afterRoots, result,
          stable, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
          afterFlags, _origin, _retained, _protects, pendingHistory, shape, returnedFits, returnedKnown⟩ :=
          SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.complete_with_history_resources_prepared seed formulas solver inventory caller before checkEmpty
            uv handle scs parentEntry edges depth free edge roots memos initial ready stored parentAvailable parentClosed realized
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
      rw [SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run,
        SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.arity_rejected checkEmpty _ _ _ _ _ scs edge caller before memos.query rejected]
    · simpa only [noCost, SourcePruningEnumerationSharedIncomingReservation.advance] using fits
    · simpa only [noCost, SourcePruningEnumerationSharedIncomingReservation.advance] using known

/-- The same prepared head retains every receipt field and its actual cache bounds. -/
theorem head_complete_cache_bounds_prepared
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
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = [])
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
        SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
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
      HeadCacheBounds before scs arity own receipt := by
  obtain ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown⟩ :=
    head_complete_resources_prepared seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored parentAvailable parentClosed realized selected
      paths counts flags pending fits reserved known
  refine ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown, ?_⟩
  have observed := running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at observed
  exact observed_head_cache_bounds checkEmpty r n p h k uv scs edge caller before memos.query
    arity own arityBound ownBound receipt observed

end MicroCFTA.SourcePruningEnumerationSharedNativeBranchCompletion
