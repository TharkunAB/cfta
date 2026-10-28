import MicroCFTA.SourcePruningEnumerationNativePreparedResources
import MicroCFTA.SourcePruningEnumerationCapturedPreparedProjectionHeap

/-!
# Projection at each original prepared native head result

The old producer retains every actual receipt and native endpoint.
The original physical row derives its projection gate.
Complete and stopped receipts retain their reached projection heap.
A literal rejected receipt retains the original native caller.
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
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem captured_rejected_caller
    {width : Nat} {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {caller returned : Caller width} {before after : Cached}
    {queries saved : Queries}
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge
      caller before queries = some (.rejected returned saved after)) : returned = caller := by
  unfold SourcePruningEnumerationCapturedEdge.run SourcePruningEnumerationSelectedEdge.run at observed
  cases prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => simp only [prepared] at observed; cases observed
  | some rows =>
      cases rows with
      | nil =>
          simp only [prepared, Option.some.injEq, SourcePruningEnumerationSelectedEdge.Result.rejected.injEq] at observed
          exact observed.1.symm
      | cons first tail =>
          cases tail with
          | cons second remaining => simp only [prepared] at observed; cases observed
          | nil =>
              rcases first with ⟨⟨symbol, staged, residual⟩, middle⟩
              simp only [prepared] at observed
              cases traversed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | stopped _fragments _observation _candidate =>
                  simp only [traversed] at observed
                  cases observed
              | complete fragments reached current children =>
                  simp only [traversed] at observed
                  cases finished : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target
                      (.node symbol fragments) (SourcePruningEnumerationSelectedEdge.finish residual (.node symbol fragments) children) with
                  | none => simp only [finished, Option.map_none] at observed; cases observed
                  | some completed => simp only [finished, Option.map_some] at observed; cases observed

/-- The same prepared head witnesses retain projection at their actual native caller. -/
theorem head_complete_resources_prepared_projection_heap
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
    (originalProjection : ProjectionHeap caller.checked.native.machine.heap) :
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
      ProjectionHeap afterCaller.checked.native.machine.heap := by
  obtain ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next, running, post, querySame,
    admitted, pendingReceipt, history, endpoint, returnedFits, returnedKnown⟩ :=
    head_complete_resources_prepared seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored parentAvailable parentClosed realized
      selected paths counts flags pending fits reserved known
  refine ⟨r, n, p, h, k, receipt, afterCaller, saved, final, next, running, post, querySame,
    admitted, pendingReceipt, history, endpoint, returnedFits, returnedKnown, ?_⟩
  have actual := running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      initial.ready.semantic.ready.semantic.1.normal.facts.linked _ parentAvailable.resident edge selected
  have rowProjection : SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none :=
    originalProjection edge.entry.key edge resident
  rcases endpoint with advanced | ⟨_unhandled, _allowed, unsupported⟩
  · by_cases allowed : arityAllows edge.children.length scs = true
    · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none => exact (rowProjection projected).elim
      | some pair =>
          rcases pair with ⟨tries, residual⟩
          have actualCost : edgeCost scs before.core.counter edge =
              SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
            simp only [edgeCost, allowed, ↓reduceIte, projected]
          have actualReserved : Reserved bits seed
              (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
            simpa only [actualCost] using reserved
          have point := SourcePruningEnumerationCapturedEdge.run_prepared_projection_heap seed formulas solver
            inventory caller before checkEmpty uv handle scs parentEntry edges depth free edge roots memos initial
            ready stored parentAvailable parentClosed realized selected paths counts flags pending allowed tries residual
            projected fits actualReserved known originalProjection r n p h k
          rw [actual] at point
          cases receipt with
          | unhandled => cases advanced
          | rejected reached current cache =>
              have originalCaller := captured_rejected_caller actual
              have reachedSame := (Prod.mk.inj (Option.some.inj advanced)).1
              rw [← reachedSame, originalCaller]
              exact originalProjection
          | complete fragment reached current cache =>
              have reachedSame := (Prod.mk.inj (Option.some.inj advanced)).1
              rw [← reachedSame]
              exact point
          | stopped fragments observation candidate =>
              rcases observation with ⟨outcome, reached, current, outer, waiting⟩
              cases outcome with
              | error _fault => cases advanced
              | ok result =>
                  cases result with
                  | none => cases advanced
                  | some raw =>
                      cases raw with
                      | cons _first _rest => cases advanced
                      | nil =>
                          cases candidate with
                          | none => cases advanced
                          | some cache =>
                              have reachedSame := (Prod.mk.inj (Option.some.inj advanced)).1
                              rw [← reachedSame]
                              exact point
    · have rejected : arityAllows edge.children.length scs = false := by
        cases value : arityAllows edge.children.length scs with
        | false => rfl
        | true => exact (allowed value).elim
      rw [SourcePruningEnumerationCapturedEdge.run,
        SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge caller before memos.query rejected] at actual
      have sameReceipt := Option.some.inj actual
      subst receipt
      have reachedSame := (Prod.mk.inj (Option.some.inj advanced)).1
      rw [← reachedSame]
      exact originalProjection
  · exact (rowProjection unsupported).elim

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
