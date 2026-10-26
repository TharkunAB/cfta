import MicroCFTA.SourcePruningEnumerationNativeBranchResources
import MicroCFTA.SourcePruningEnumerationCapturedEdgeScalarBounds

namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeBranches (advance)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {width bits : Nat}

/-- Bound each actual receipt cache from the captured input and original edge widths. -/
def HeadCacheBounds (before : Cached) (scs : List Suspended) (arity own : Nat) : Receipt width → Prop
  | .complete _ _ _ after | .rejected _ _ after =>
      after.core.counter ≤ before.core.counter + own + arity ∧
        suspendedBound after.core ≤ suspendedBound before.core + arity * (scs.length + own)
  | .stopped _ _ candidate =>
      ∀ after, candidate = some after →
        after.core.counter ≤ before.core.counter + own + arity ∧
          suspendedBound after.core ≤ suspendedBound before.core + arity * (scs.length + own)
  | .unhandled => True

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original arity and projection widths bound every actual captured-edge cache receipt. -/
theorem observed_head_cache_bounds
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (arity own : Nat) (arityBound : edge.children.length ≤ arity)
    (ownBound : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
        tries.length ≤ own)
    (receipt : Receipt width)
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge
      caller before queries = some receipt) :
    HeadCacheBounds before scs arity own receipt := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        rw [SourcePruningEnumerationCapturedEdge.run,
          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty r n p h k scs edge caller before queries
            allowed projected] at observed
        cases Option.some.inj observed
        trivial
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        have ownLe := ownBound tries residual projected
        have counterCeiling : before.core.counter + tries.length + edge.children.length ≤
            before.core.counter + own + arity := by omega
        have massCeiling : suspendedBound before.core + edge.children.length * (scs.length + tries.length) ≤
            suspendedBound before.core + arity * (scs.length + own) :=
          Nat.add_le_add_left (Nat.mul_le_mul arityBound (Nat.add_le_add_left ownLe scs.length)) _
        have bounds := SourcePruningEnumerationCapturedEdge.observed_scalar_bounds
          checkEmpty r n p h k target scs edge caller before queries tries residual projected
        rw [observed] at bounds
        cases receipt with
        | unhandled => trivial
        | complete _ _ _ after | rejected _ _ after =>
            exact ⟨Nat.le_trans bounds.1 counterCeiling, Nat.le_trans bounds.2 massCeiling⟩
        | stopped _ _ candidate =>
            intro after attached
            obtain ⟨counter, mass⟩ := bounds after attached
            exact ⟨Nat.le_trans counter counterCeiling, Nat.le_trans mass massCeiling⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    rw [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge caller before queries
        rejected] at observed
    cases Option.some.inj observed
    exact ⟨by omega, Nat.le_add_right _ _⟩

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
      HeadCacheBounds before scs arity own receipt := by
  obtain ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown⟩ :=
    head_complete_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
      paths counts flags pending fits reserved known
  refine ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next,
    running, post, queries, admitted, pendingHistory, history, shape, returnedFits, returnedKnown, ?_⟩
  have observed := running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at observed
  exact observed_head_cache_bounds checkEmpty r n p h k uv scs edge caller before memos.query
    arity own arityBound ownBound receipt observed

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
