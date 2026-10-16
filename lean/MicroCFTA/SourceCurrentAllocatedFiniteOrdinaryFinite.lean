import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryExecution
import MicroCFTA.InternedNormalizationFree

/-!
# Finite checked requests on finite ordinary inputs

Finite ordinary structure gives original syntax. Coherent readback and
available child records give empty cached free-name lists. Initial physical
readiness then constructs a finite checked trace. Structural verification
uses that same trace and retains the warm result certificates.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedFiniteOrdinaryCode SourceCurrentAllocatedFiniteOrdinaryStored
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open MergedOrdinaryHeight (height)

section Structure
variable {Symbol Guard : Type}

/-- Finite ordinary records contain only original payload syntax. -/
theorem original (value : Value Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value) : Original value := by
  cases domain with
  | empty => exact .empty
  | @ordinary edges entry depth free rows =>
      apply Original.node
      intro edge present child member
      exact original child ((rows.member edge present).member child member)
termination_by height value
decreasing_by exact MergedOrdinaryHeight.child_lt _ _ _ _ edge present child member

/-- Coherent available ordinary records have no cached free names. -/
theorem closed (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value) : value.free = [] := by
  induction available with
  | intro value resident issued children ih =>
      cases domain with
      | empty => rfl
      | @ordinary edges entry depth free rows =>
          change free = []
          rw [InternedNormalizationFree.node_free state coherent entry edges depth free resident]
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro name named
          obtain ⟨child, present, occurs⟩ := (childFree_member _ name).mp named
          obtain ⟨edge, inside, member⟩ := List.mem_flatMap.mp present
          have noNames := ih child present ((rows.member edge inside).member child member)
          rw [noNames] at occurs
          cases occurs

end Structure

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

private theorem trace_semantic [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {A : Type} {fuel : Nat} {control rest : SourceEqualityNativeDemand.Control A}
    {before after : Checked width} (trace : Trace fuel control before rest after)
    (semantic : SemanticReady before.native.machine.heap) : SemanticReady after.native.machine.heap := by
  induction trace with
  | refl => exact semantic
  | cons control before next middle final after count inputs one tail ih =>
      have current := SourceCurrentAllocatedNativeSemanticHeap.step_semantic control before semantic
        (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs)
      rw [one] at current
      exact ih current

/-- Initial resident domain operands construct one finite checked return with both height bounds. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (state : Checked width)
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node left)
    (rightDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node right)
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state value after
        (fun final value => Available final.heap value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ SemanticReady after.native.machine.heap ∧
      Stored after.native ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧
      height value ≤ height left ∧ height value ≤ height right ∧ value.free = [] := by
  have coherent := good.native.machine.1.coherent
  obtain ⟨fuel, value, after, receipt, afterIdle⟩ :=
    SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete holds state good idle left right
      (original left leftDomain) (original right rightDomain) leftAvailable rightAvailable
      (closed state.native.machine.heap coherent left leftAvailable leftDomain)
      (closed state.native.machine.heap coherent right rightAvailable rightDomain) ranges
  have resultDomain := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state after fuel value receipt.trace good semantic stored
    ⟨rfl, leftDomain, rightDomain⟩
  exact ⟨fuel, value, after, receipt, afterIdle, trace_semantic receipt.trace semantic, resultDomain.1,
    resultDomain.2.1, resultDomain.2.2.1, resultDomain.2.2.2,
    closed after.native.machine.heap receipt.good.native.machine.1.coherent value receipt.result resultDomain.2.1⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite
