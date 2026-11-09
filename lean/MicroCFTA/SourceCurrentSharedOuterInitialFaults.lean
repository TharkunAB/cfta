import MicroCFTA.SourceCurrentSharedOuterLocalFaults
import MicroCFTA.SourceCurrentSharedOuterInitialParentFailure
import MicroCFTA.SourceCurrentSharedOuterInitialEdgeMemoFailure

/-!
# Remaining diagnostics at initialized shared outer outcomes

One initial reservation and adequate lower bounds exclude Parent faults.
An initially idle edge table also excludes edge memo diagnostics.
The remaining outcomes are outer exhaustion, node memo diagnostics and
unexpected references. Node collision and closed-input proofs remain open.
-/
namespace MicroCFTA.SourceCurrentSharedOuterInitialFaults
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentSharedOuterExecutionAncestry (caller)
open SourceCurrentSharedOuterPrefixInvariants (Inputs)
open SourceCurrentSharedOuterEdgeIdle (EdgeIdle)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {bits : Nat}

/-- Actual initialized faults have only the remaining outer diagnostic forms. -/
theorem failed_cases
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget : Nat} {first : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2)
    (idle : EdgeIdle (caller first))
    (gBound : phaseNeed budget first seed ≤ g) (sBound : phaseNeed budget first seed ≤ s)
    (rBound : phaseNeed budget first seed ≤ r) (eBound : phaseNeed budget first seed ≤ e)
    (pBound : phaseNeed budget first seed ≤ p) (hBound : phaseNeed budget first seed ≤ h)
    (mBound : phaseNeed budget first seed ≤ m) (cBound : phaseNeed budget first seed ≤ c)
    (nBound : phaseNeed budget first seed ≤ n)
    (fault : SourceCurrentAllocatedSharedPartialWorker.Fault (bits+2))
    (after : SourceCurrentAllocatedPartialState.State (bits+2))
    (actual : SourceCurrentSharedOuterActiveAncestry.run g s r e p h m c n budget first =
      .failed fault after) :
    (∃ limit, fault = .exhausted limit) ∨
    (∃ handle, fault = .nodeMemo handle .busy ∨ fault = .nodeMemo handle .absent) ∨
    (∃ name, fault = .unexpectedReference name) := by
  rcases SourceCurrentSharedOuterLocalFaults.failed_cases formulas solver seed
      initial frame fits known inputs room fault after actual with
    exhausted | nodeMemo | edgeMemo | reference | parent
  · exact Or.inl exhausted
  · exact Or.inr (Or.inl nodeMemo)
  · obtain ⟨handle,observation,rfl⟩ := edgeMemo
    exact False.elim (SourceCurrentSharedOuterInitialEdgeMemoFailure.no_edge_memo_failure
      formulas solver seed initial frame fits known inputs room idle handle observation after actual)
  · exact Or.inr (Or.inr reference)
  · obtain ⟨observation,rfl⟩ := parent
    exact False.elim (SourceCurrentSharedOuterInitialParentFailure.no_parent_failure
      formulas solver seed initial frame fits known inputs room
      gBound sBound rBound eBound pBound hBound mBound cBound nBound observation after actual)

end MicroCFTA.SourceCurrentSharedOuterInitialFaults
