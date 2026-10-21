import MicroCFTA.SourceCurrentOuterLocalFaults
import MicroCFTA.SourceCurrentOuterInitialParentFailure
import MicroCFTA.SourceCurrentOuterInitialEdgeMemoFailure
import MicroCFTA.SourceCurrentOlderOwnerBusy
import MicroCFTA.SourceCurrentOuterReferenceAbsent
namespace MicroCFTA.SourceCurrentOuterDoneOrExhausted
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
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "phaseNeed" => SourceCurrentOuterInitialFuel.phaseNeed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}

/-- The same bounded outer phase either returns or reports its outer-fuel limit. -/
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
    (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))
    (stored : SourceCurrentOuterClosedInputs.NodeStored (caller first))
    (closed : SourceCurrentOuterClosedInputs.InputsClosed first)
    (initialNodeIdle : ∀ chosen owner,
      (caller first).nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩)
    (initialEdgeIdle : SourceCurrentOuterEdgeIdle.EdgeIdle (caller first))
    (gBound : phaseNeed budget first seed ≤ g) (sBound : phaseNeed budget first seed ≤ s)
    (rBound : phaseNeed budget first seed ≤ r) (eBound : phaseNeed budget first seed ≤ e)
    (pBound : phaseNeed budget first seed ≤ p) (hBound : phaseNeed budget first seed ≤ h)
    (mBound : phaseNeed budget first seed ≤ m) (cBound : phaseNeed budget first seed ≤ c)
    (nBound : phaseNeed budget first seed ≤ n) :
    (∃ after, SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first =
      .done () after) ∨
    (∃ limit after, SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first =
      .failed (.exhausted limit) after) := by
  cases actual : SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first with
  | done value after =>
    cases value
    exact Or.inl ⟨after,rfl⟩
  | failed fault after =>
    rcases SourceCurrentOuterLocalFaults.failed_cases formulas solver seed initial frame fits known inputs room
      fault after actual with exhausted | nodeMemo | edgeMemo | reference | parent
    · obtain ⟨limit,rfl⟩ := exhausted
      exact Or.inr ⟨limit,after,rfl⟩
    · rcases nodeMemo with ⟨handle,busy | absent⟩
      · subst fault
        exact False.elim (SourceCurrentOlderOwnerBusy.no_node_busy formulas solver seed initial frame fits known inputs room
          normal supported causal merged positiveMemo origins initialNodeIdle after actual)
      · subst fault
        exact False.elim ((SourceCurrentOuterReferenceAbsent.no_reference_or_node_absent formulas solver seed initial frame fits known inputs room
          normal supported causal merged positiveMemo origins stored closed .depth handle after).2 actual)
    · obtain ⟨handle,observation,rfl⟩ := edgeMemo
      exact False.elim (SourceCurrentOuterInitialEdgeMemoFailure.no_edge_memo_failure formulas solver seed initial frame fits known inputs room
        initialEdgeIdle handle observation after actual)
    · obtain ⟨name,rfl⟩ := reference
      exact False.elim ((SourceCurrentOuterReferenceAbsent.no_reference_or_node_absent formulas solver seed initial frame fits known inputs room
        normal supported causal merged positiveMemo origins stored closed name 0 after).1 actual)
    · obtain ⟨observation,rfl⟩ := parent
      exact False.elim (SourceCurrentOuterInitialParentFailure.no_parent_failure formulas solver seed initial frame fits known inputs room
        gBound sBound rBound eBound pBound hBound mBound cBound nBound observation after actual)

end MicroCFTA.SourceCurrentOuterDoneOrExhausted

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentOuterDoneOrExhausted.done_or_exhausted
#print MicroCFTA.SourceCurrentOuterDoneOrExhausted.done_or_exhausted
#print axioms MicroCFTA.SourceCurrentOuterDoneOrExhausted.done_or_exhausted
