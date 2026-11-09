import MicroCFTA.SourceCurrentSharedOuterInitialFaults
import MicroCFTA.SourceCurrentSharedOlderOwnerBusy
import MicroCFTA.SourceCurrentSharedOuterReferenceAbsent

/-!
# Remaining outcomes of the actual shared outer worker

Initial resource and closed-input facts exclude every diagnostic except
outer-fuel exhaustion. These laws do not assert sufficient outer fuel.
-/
namespace MicroCFTA.SourceCurrentSharedOuterDoneOrExhausted
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentSharedOuterExecutionAncestry.caller
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}

/-- Every actual failed phase reports only its outer-fuel limit. -/
theorem failed_exhausted
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget : Nat} {first : Phase (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : SourceCurrentSharedOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentSharedOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentSharedResourceParentWriters.Origins formulas solver (caller first))
    (stored : SourceCurrentSharedOuterClosedInputs.NodeStored (caller first))
    (closed : SourceCurrentSharedOuterClosedInputs.InputsClosed first)
    (initialNodeIdle : ∀ chosen owner,
      (caller first).nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩)
    (initialEdgeIdle : SourceCurrentSharedOuterEdgeIdle.EdgeIdle (caller first))
    (gBound : phaseNeed budget first seed ≤ g) (sBound : phaseNeed budget first seed ≤ s)
    (rBound : phaseNeed budget first seed ≤ r) (eBound : phaseNeed budget first seed ≤ e)
    (pBound : phaseNeed budget first seed ≤ p) (hBound : phaseNeed budget first seed ≤ h)
    (mBound : phaseNeed budget first seed ≤ m) (cBound : phaseNeed budget first seed ≤ c)
    (nBound : phaseNeed budget first seed ≤ n)
    (fault : SourceCurrentAllocatedSharedPartialWorker.Fault (bits + 2))
    (after : Caller (bits + 2))
    (actual : SourceCurrentSharedOuterActiveAncestry.run g s r e p h m c n budget first =
      .failed fault after) :
    ∃ limit, fault = .exhausted limit := by
  rcases SourceCurrentSharedOuterInitialFaults.failed_cases formulas solver seed
      initial frame fits known inputs room initialEdgeIdle
      gBound sBound rBound eBound pBound hBound mBound cBound nBound
      fault after actual with exhausted | nodeMemo | reference
  · exact exhausted
  · rcases nodeMemo with ⟨handle,busy | absent⟩
    · subst fault
      exact False.elim (SourceCurrentSharedOlderOwnerBusy.no_node_busy formulas solver seed
        initial frame fits known inputs room normal supported causal merged positiveMemo origins
        initialNodeIdle after actual)
    · subst fault
      exact False.elim ((SourceCurrentSharedOuterReferenceAbsent.no_reference_or_node_absent
        formulas solver seed initial frame fits known inputs room normal supported causal merged
        positiveMemo origins stored closed .depth handle after).2 actual)
  · obtain ⟨name,rfl⟩ := reference
    exact False.elim ((SourceCurrentSharedOuterReferenceAbsent.no_reference_or_node_absent
      formulas solver seed initial frame fits known inputs room normal supported causal merged
      positiveMemo origins stored closed name 0 after).1 actual)

/-- The actual bounded phase returns or reports its outer-fuel limit. -/
theorem done_or_exhausted
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget : Nat} {first : Phase (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : SourceCurrentSharedOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentSharedOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentSharedResourceParentWriters.Origins formulas solver (caller first))
    (stored : SourceCurrentSharedOuterClosedInputs.NodeStored (caller first))
    (closed : SourceCurrentSharedOuterClosedInputs.InputsClosed first)
    (initialNodeIdle : ∀ chosen owner,
      (caller first).nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩)
    (initialEdgeIdle : SourceCurrentSharedOuterEdgeIdle.EdgeIdle (caller first))
    (gBound : phaseNeed budget first seed ≤ g) (sBound : phaseNeed budget first seed ≤ s)
    (rBound : phaseNeed budget first seed ≤ r) (eBound : phaseNeed budget first seed ≤ e)
    (pBound : phaseNeed budget first seed ≤ p) (hBound : phaseNeed budget first seed ≤ h)
    (mBound : phaseNeed budget first seed ≤ m) (cBound : phaseNeed budget first seed ≤ c)
    (nBound : phaseNeed budget first seed ≤ n) :
    (∃ after, SourceCurrentSharedOuterActiveAncestry.run g s r e p h m c n budget first =
      .done () after) ∨
    (∃ limit after, SourceCurrentSharedOuterActiveAncestry.run g s r e p h m c n budget first =
      .failed (.exhausted limit) after) := by
  cases actual : SourceCurrentSharedOuterActiveAncestry.run g s r e p h m c n budget first with
  | done value after =>
    cases value
    exact Or.inl ⟨after,rfl⟩
  | failed fault after =>
    obtain ⟨limit,rfl⟩ := failed_exhausted formulas solver seed initial frame fits known inputs room
      normal supported causal merged positiveMemo origins stored closed initialNodeIdle initialEdgeIdle
      gBound sBound rBound eBound pBound hBound mBound cBound nBound fault after actual
    exact Or.inr ⟨limit,after,rfl⟩

end MicroCFTA.SourceCurrentSharedOuterDoneOrExhausted
