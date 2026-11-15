import MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult
import MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback
import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourceEqualityNativeDemandMismatchReceipt

/-!
# Actual mismatched edge queries return a discarded sentinel row

The checked query supplies its original key check and dispatch prefix.
The mismatch body reaches the sentinel before any source field lookup.
Its canonical execution fixes the empty child at the actual body result.
A warm ready hit uses the prior returned clause at the same request.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMismatchRowQuery
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat}

set_option autoImplicit false

/-- A real mismatched edge query returns the literal empty child and is removed by surviving. -/
theorem mismatched_row_query_sentinel
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (fuel traceFuel : Nat) (result : EdgeValue Symbol Guard)
    (physical : Physical before.native)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (returned : Returned (fun old row => old = request → row.children = [.empty]) before.native.edges)
    (done : execute fuel (.code (requestEdge request.domain request.left request.right)) before = .done result after)
    (actual : Trace traceFuel (.code (requestEdge request.domain request.left request.right)) before
      (.code (.pure result)) after) :
    result.children = [.empty] ∧ surviving [result] = [] := by
  let law : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop :=
    fun old row => old = request → row.children = [.empty]
  have inputs := SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs actual
  change EdgeReady before.native.machine request ∧
    SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right at inputs
  have queryLaw := SourceCurrentAllocatedNativeEdgeQueryResult.edge_query_result_of_body_induction
    law request before after fuel result physical inputs.1 inputs.2 returned done
    (by
      intro bodySteps _bodyBound _next first middle value origin bodyRaw
      intro _
      obtain ⟨_tailFuel, _traceCount, dispatchPhysical, _tailPhysical⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix origin actual
      have firstPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension dispatchPhysical physical
      let built := run (makeEdge request.left.entry.key.symbol top [.empty]) first.native.machine.heap
      let sentinelAfter : Checked width :=
        ⟨advance first.native {first.native.machine with heap := built.2},
          SourceEqualityMkEdgeAllocation.emptyField first.operations⟩
      have canonical : execute 3 (.edgeBody request .pure) first = .done built.1 sentinelAfter :=
        SourceEqualityNativeDemandMismatchReceipt.mismatch_body_complete request first mismatch
      have observed := trace_done bodySteps (.edgeBody request .pure) first middle value bodyRaw
      have observedLater := done_stable (bodySteps + 1) 3 (.edgeBody request .pure)
        first middle value observed
      have canonicalLater := done_stable 3 (bodySteps + 1) (.edgeBody request .pure)
        first sentinelAfter built.1 canonical
      have same : Outcome.done value middle = .done built.1 sentinelAfter :=
        observedLater.symm.trans (by simpa only [Nat.add_comm] using canonicalLater)
      have available : InternedNestedProvenance.Values first.native.machine.heap
          ([.empty] : List (Value Symbol Guard)) := by
        intro child member
        have childEq := List.mem_singleton.mp member
        subst child
        exact empty_available _
      have fields := InternedGuardedExecutionLists.makeEdge_fields request.left.entry.key.symbol top [.empty]
        first.native.machine.heap firstPhysical.1.machine.1.coherent firstPhysical.1.machine.1.cached available
      rw [(Outcome.done.inj same).1]
      exact fields.2)
  have children : result.children = [.empty] := queryLaw rfl
  refine ⟨children, ?_⟩
  simp [surviving, children, Value.referenceOf]

end MicroCFTA.SourceCurrentAllocatedNativeMismatchRowQuery
