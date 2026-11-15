import MicroCFTA.SourceEqualityNativeDemandMismatchReceipt
import MicroCFTA.SourceEqualityNativeDemandTraceSplit
import MicroCFTA.SourceRecursiveIntersectionCompile
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.InternedEmptyNormalization
import MicroCFTA.InternedGuardedExecutionLists

/-!
# Raw checked body result laws for native history induction

Closed equal operands select empty, reset, or self before all payload cases.
Only the actual reset query needs a smaller pure-trace result hypothesis.
That query uses the same body step count and the original outer budget.
Arity mismatches return the exact sentinel and reached checked state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRawBodyResults
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (hasEmpty reset closedSelf empty_first reset_first self_first)
open SourceEqualityNativeDemand
open InternedNestedProvenance (Values)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat}

set_option autoImplicit false

/-- Every raw completed closed-self body returns the original value through its actual smaller reset query. -/
theorem compile_node_closed_self_trace_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (original bodyState after : Checked width)
    (parentFuel bodySteps : Nat) (result : Value Symbol Guard)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (entered : Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) bodyState)
    (smaller : bodySteps < parentFuel)
    (actual : Steps bodySteps (.code (compileNode request)) bodyState (.code (.pure result)) after)
    (resetChild : ∀ childSteps, childSteps < parentFuel →
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (value : Value Symbol Guard) (middle : Checked width),
      Steps 1 (.code (.node request .pure)) original
        (.code ((requestNode IntersectionEmptyDomain.emptyDomain request.left request.left).bind next)) bodyState →
      Steps childSteps (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.left))
        bodyState (.code (.pure value)) middle →
      request.left.free = [] → value = request.left) :
    request.right = request.left → request.left.free = [] → result = request.left := by
  intro same closed
  have selfGuard : closedSelf request.left request.right = true := by
    simp [closedSelf, same, closed]
  cases emptyCase : hasEmpty request.left request.right with
  | false =>
      cases restart : reset request.domain.key request.left request.right with
      | false =>
          have selected := self_first request.domain.key request.left request.right emptyCase restart selfGuard
          have compiled : compileNode request = .pure request.left := by
            simp only [compileNode, selected]
          have terminal : Steps bodySteps (.code (.pure request.left)) bodyState (.code (.pure result)) after := by
            simpa only [compiled] using actual
          exact (pure_trace bodySteps request.left result bodyState after terminal).2.1.symm
      | true =>
          have selected := reset_first request.domain.key request.left request.right emptyCase restart
          have compiled : compileNode request =
              requestNode IntersectionEmptyDomain.emptyDomain request.left request.left := by
            simp only [compileNode, selected]
            rw [same]
          have origin : Steps 1 (.code (.node request .pure)) original
              (.code ((requestNode IntersectionEmptyDomain.emptyDomain request.left request.left).bind finishNext)) bodyState := by
            simpa only [compiled] using entered
          have child : Steps bodySteps
              (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.left))
              bodyState (.code (.pure result)) after := by
            simpa only [compiled] using actual
          exact resetChild bodySteps smaller finishNext result after origin child closed
  | true =>
      have emptyReference : request.left.referenceOf = .empty := by
        simpa [hasEmpty, same] using emptyCase
      have emptyValue : request.left = .empty :=
        (InternedEmptyNormalization.reference_empty request.left).mp emptyReference
      have selected := empty_first request.domain.key request.left request.right emptyCase
      have compiled : compileNode request = .pure .empty := by
        simp only [compileNode, selected]
      have terminal : Steps bodySteps (.code (.pure (.empty : Value Symbol Guard)))
          bodyState (.code (.pure result)) after := by
        simpa only [compiled] using actual
      exact (pure_trace bodySteps .empty result bodyState after terminal).2.1.symm.trans emptyValue.symm

/-- A raw mismatched body trace returns the real sentinel and its exact full endpoint from weak physical validity. -/
theorem mismatch_edge_body_trace_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width) (bodySteps : Nat)
    (row : EdgeValue Symbol Guard) (physical : Physical before.native)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (actual : Steps bodySteps (.edgeBody request .pure) before (.code (.pure row)) after) :
    let built := run (makeEdge request.left.entry.key.symbol top [.empty]) before.native.machine.heap
    row.children = [.empty] ∧ row = built.1 ∧
      after = ⟨advance before.native {before.native.machine with heap := built.2},
        SourceEqualityMkEdgeAllocation.emptyField before.operations⟩ := by
  let built := run (makeEdge request.left.entry.key.symbol top [.empty]) before.native.machine.heap
  let endpoint : Checked width :=
    ⟨advance before.native {before.native.machine with heap := built.2},
      SourceEqualityMkEdgeAllocation.emptyField before.operations⟩
  have standard : SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) before = .done built.1 endpoint :=
    SourceEqualityNativeDemandMismatchReceipt.mismatch_body_complete request before mismatch
  have completed := trace_done bodySteps _ before after row actual
  have first := done_stable (bodySteps + 1) 3 _ before after row completed
  have second := done_stable 3 (bodySteps + 1) _ before endpoint built.1 standard
  rw [Nat.add_comm 3 (bodySteps + 1)] at second
  have equal := Outcome.done.inj (first.symm.trans second)
  have available : Values before.native.machine.heap ([.empty] : List (Value Symbol Guard)) := by
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact empty_available before.native.machine.heap
  have fields := InternedGuardedExecutionLists.makeEdge_fields request.left.entry.key.symbol top [.empty]
    before.native.machine.heap physical.machine.1.coherent physical.machine.1.cached available
  refine ⟨?_, equal.1, equal.2⟩
  rw [equal.1]
  exact fields.2

end MicroCFTA.SourceCurrentAllocatedNativeRawBodyResults

set_option warningAsError true
#check MicroCFTA.SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
#print axioms MicroCFTA.SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
#check MicroCFTA.SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
#print axioms MicroCFTA.SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
