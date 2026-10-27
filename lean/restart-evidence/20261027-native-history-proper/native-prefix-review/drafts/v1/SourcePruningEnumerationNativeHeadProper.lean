import MicroCFTA.SourcePruningEnumerationNativeBranchResources
import MicroCFTA.SourcePruningEnumerationCapturedEdgeEndpointProper

/-!
# Proper storage in actual native head receipts

The original resource packet keeps its full native endpoint and memos.
Original proper storage derives proper storage in every attached receipt cache.
The actual dispatcher supplies rejection and unsupported cases.
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

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual head observation preserves proper storage in each attached cache. -/
theorem observed_cache_proper
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
    (proper : EnumerationProgress.ProperState before.core)
    {r n p h k : Nat} {receipt : Receipt (bits + 2)}
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k uv scs edge caller before memos.query =
      some receipt) :
    match (generalizing := false) receipt with
        | .complete _ _ _ after | .rejected _ _ after => EnumerationProgress.ProperState after.core
        | .stopped _ _ (some after) => EnumerationProgress.ProperState after.core
        | _ => True := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        rw [SourcePruningEnumerationCapturedEdge.run,
          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty r n p h k scs edge caller before memos.query
            allowed projected] at observed
        cases observed
        trivial
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        exact SourcePruningEnumerationCapturedEdge.observed_cache_proper formulas solver inventory caller before checkEmpty
          uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
          selected paths counts flags pending allowed tries residual projected proper observed
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    rw [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge caller before memos.query
        rejected] at observed
    cases observed
    exact proper

/-- Keep the full original head resource packet and derive proper receipt caches. -/
theorem head_complete_resources_proper
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
      ((∀ er en P H ek, p ≤ P → h ≤ H →
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
        afterCaller.checked.native.machine.heap) ∧
      (EnumerationProgress.ProperState before.core →
      match (generalizing := false) receipt with
        | .complete _ _ _ after | .rejected _ _ after => EnumerationProgress.ProperState after.core
        | .stopped _ _ (some after) => EnumerationProgress.ProperState after.core
        | _ => True) := by
  obtain ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, querySame, admitted, pendingHistory, fragmentHistory, shape, returnedFits, returnedKnown⟩ :=
    head_complete_resources seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
      paths counts flags pending fits reserved known
  refine ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    ⟨running, post, querySame, admitted, pendingHistory, fragmentHistory, shape, returnedFits, returnedKnown⟩, ?_⟩
  intro proper
  exact observed_cache_proper formulas solver inventory caller before checkEmpty
    uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
    paths counts flags pending proper
    (by simpa only [Nat.add_zero] using running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _))

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
