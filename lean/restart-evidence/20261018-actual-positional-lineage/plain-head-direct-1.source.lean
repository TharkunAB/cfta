import MicroCFTA.SourceCurrentRequiredGuardOrigins
import MicroCFTA.SourceCurrentAllocatedSharedEditWorker
import MicroCFTA.SourceEqualityRequiredWorkerSound
import MicroCFTA.SourceCurrentOuterGuardHeapReturns

/-!
# Empty effective own fields from actual accepted recursive Heads

The initial heap premise records causal Mu body-to-probe guard profiles.
It does not require every resident raw edge guard to be plain. Actual Head
and Required worker returns derive their own completed graphs. A positive
returned row therefore excludes an accepted recursive source branch.
These results do not prove recursive completion or outer termination.
-/
namespace MicroCFTA.SourceCurrentActualPlainHeadOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityRequiredGraph SourceEqualityRequiredHead
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Heap" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "Good" => SourceCurrentNativeOperationHeap.Good
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem head_ordinary {value result : Node} {before after : State Symbol Guard}
    (actual : Head value before result after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Available before value) :
    SourceEqualityRequiredCache.Ordinary result := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
    have read := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
    have middleSemantic : SourceEqualityRequiredSemanticCache.SemanticReady middle := by
      simpa only [exposed, MergedSourceExposure.Result.state] using read.semantic
    have ordinary := SourceEqualityRequiredCache.node_ordinary edges middle
      middleSemantic.ready.semantic.1.normal.facts (read.rows _ _ exposed)
    simpa only [rebuilt] using ordinary

/-- Actual accepted Head returns ordinary rows with empty effective own fields in a mixed heap. -/
theorem head {before : Checked width} {value result : Node} {after : State Symbol Guard}
    (actual : Head value before.native.machine.heap result after)
    (good : Good before) (guards : Heap before.native.machine.heap)
    (available : Available before.native.machine.heap value)
    (accepted : SourceMemoGate.unconstrained value = true) :
    Heap after ∧ SourceEqualityRequiredCache.Keeps before.native.machine.heap after ∧
      Available after result ∧ SourceEqualityRequiredCache.Ordinary result ∧
      ∀ row ∈ nodeEdges result, SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some []) := by
  have localResult := SourceCurrentRequiredGuardOrigins.accepted_head actual good.semantic good.costs available guards accepted
  have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) actual good.semantic good.costs
    (fun _ _ _ => trivial) available
  exact ⟨localResult.1, effects.1, effects.2.2.2.2,
    head_ordinary actual good.semantic good.costs available, localResult.2.2⟩

/-- A literal current shared Head worker derives its exact graph and empty effective own rows. -/
theorem shared_head {fuel : Nat} {before after : SourceCurrentAllocatedSharedTargetState.State width}
    {value result : Node}
    (actual : SourceCurrentAllocatedSharedEditWorker.head fuel value before = .done result after)
    (good : Good before.checked) (guards : Heap before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap value)
    (accepted : SourceMemoGate.unconstrained value = true) :
    Head value before.checked.native.machine.heap result after.checked.native.machine.heap ∧
      Heap after.checked.native.machine.heap ∧ SourceEqualityRequiredCache.Ordinary result ∧
      ∀ row ∈ nodeEdges result, SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some []) := by
  cases returned : SourceEqualityRequiredWorker.head fuel value before.checked.native.machine.heap with
  | pending | unresolved | exhausted =>
    simp only [SourceCurrentAllocatedSharedEditWorker.head, returned] at actual
    cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedSharedEditWorker.head, returned] at actual
    cases actual
    have graph := SourceEqualityRequiredWorkerSound.head_graph fuel value _ _ heap returned
    have verified := head graph good guards available accepted
    exact ⟨graph, verified.1, verified.2.2.2.1, verified.2.2.2.2⟩

/-- A literal Required return on an accepted input derives its graph and empty effective own rows. -/
theorem required {fuel readFuel : Nat} {needed : SourceEqualityNeeded.Needed}
    {before : Checked width} {value result : Node} {after : State Symbol Guard}
    (actual : SourceEqualityRequiredWorker.require fuel readFuel needed value before.native.machine.heap = .done result after)
    (good : Good before) (guards : Heap before.native.machine.heap)
    (available : Available before.native.machine.heap value)
    (accepted : SourceMemoGate.unconstrained value = true) :
    RequireNode needed value before.native.machine.heap result after ∧ Heap after ∧
      ∀ row ∈ nodeEdges result, SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some []) := by
  have graph := SourceEqualityRequiredWorkerSound.require_graph fuel readFuel needed value _ result after actual
  have verified := SourceCurrentRequiredGuardOrigins.accepted_node graph good.semantic good.costs available guards accepted
  exact ⟨graph, verified.1, verified.2.2⟩

/-- A positive returned row comes from an indexed ordinary source row when recursive input passes its gate. -/
theorem positive_ordinary {needed : SourceEqualityNeeded.Needed} {before : Checked width}
    {value result : Node} {after : State Symbol Guard} {row : Edge} {classes : EqualityNormalize.Constraints}
    (actual : RequireNode needed value before.native.machine.heap result after)
    (good : Good before) (guards : Heap before.native.machine.heap)
    (available : Available before.native.machine.heap value)
    (accepted : Recursive value → SourceMemoGate.unconstrained value = true)
    (member : row ∈ nodeEdges result)
    (positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some classes)) (nonempty : classes ≠ []) :
    ∃ entry originals depth free, value = .node entry originals depth free ∧
      ∃ index : Nat, ∃ original, originals[index]? = some original ∧
        SourceCurrentRequiredGuardOrigins.RowOrigin original row := by
  have exclude (recursive : Recursive value) : False := by
    have verified := SourceCurrentRequiredGuardOrigins.accepted_node actual good.semantic good.costs available guards (accepted recursive)
    have plain := verified.2.2 row member
    exact nonempty (by simpa only [Except.ok.injEq, Option.some.injEq] using positive.symm.trans plain)
  cases value with
  | node entry originals depth free =>
    obtain ⟨original, included, origin⟩ :=
      SourceCurrentRequiredGuardOrigins.ordinary actual good.semantic good.costs available row member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp included
    exact ⟨entry, originals, depth, free, rfl, index, original, found, origin⟩
  | mu | union => exact False.elim (exclude trivial)
  | empty =>
    cases actual with
    | identity => cases member
    | empty => cases member
    | recursive _ recursive => cases recursive
  | reference =>
    cases actual with
    | identity => cases member
    | recursive _ recursive => cases recursive

section Prefix
variable [DecidableEq Symbol] [DecidableEq Node]
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached)
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

/-- An actual outer prefix supplies current physical and causal facts for an observed accepted Head. -/
theorem reached_head {g s r e p h m c n budget fuel : Nat} {first : Phase width}
    {request : SourceCurrentAllocatedPartialState.NodeRequest}
    {before : SourceCurrentAllocatedPartialState.State width} {result : Node} {after : State Symbol Guard}
    (prefixTrace : Reached g s r e p h m c n budget first (.body fuel request before))
    (good : SourceCurrentOuterPrefixInvariants.Good (caller first))
    (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
    (guards : Heap (caller first).checked.native.machine.heap)
    (actual : Head request.value before.checked.native.machine.heap result after)
    (accepted : SourceMemoGate.unconstrained request.value = true) :
    Heap after ∧ SourceEqualityRequiredCache.Keeps before.checked.native.machine.heap after ∧
      Available after result ∧ SourceEqualityRequiredCache.Ordinary result ∧
      ∀ row ∈ nodeEdges result, SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some []) := by
  have current := SourceCurrentOuterPrefixInvariants.reached prefixTrace good inputs
  have currentGuards := SourceCurrentOuterGuardHeapReturns.reached Plain prefixTrace good inputs guards
  exact head actual current.1.checked currentGuards current.2.2 accepted
end Prefix

end MicroCFTA.SourceCurrentActualPlainHeadOrigins
