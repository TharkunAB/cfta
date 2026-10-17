import MicroCFTA.SourceCurrentUnionNormalLocalParent
import MicroCFTA.SourceCurrentRequiredUnionNormalNative
import MicroCFTA.SourceCurrentRequiredUnionNormalRead
import MicroCFTA.SourceCurrentAllocatedNativeWidthTrace
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.all true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.UnionLocalOptionalKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "initialBound" => InternedValueMassHeap.initialBound
local notation "Stored" => InternedValueMassHeap.Stored
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def base : Syntax Symbol Guard := .node [.mk ("base",.top) top []]
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def pair : Nat × Nat := (7,9)
private def openExpression : Syntax Symbol Guard :=
  .node [.mk ("step",.top) top [.var 0,.binder false (.union [base,.var 0])]]
private def openBuilt := InternedFreshOrdinaryConstruction.build openExpression
  [.reference (.intersection pair.1 pair.2)] empty
private def body : Value Symbol Guard := match openBuilt with | .done value _ => value | .pending .. => .empty
private def openHeap := openBuilt.state
private def optional := SourceRecursiveIntersectionMaybeMu.maybeMu pair body openHeap
private def recursiveValue : Value Symbol Guard := match optional with | .done value _ => value | .pending .. => .empty
private def optionalHeap := optional.state
private def optionalBefore : Checked 10 := ⟨initial 10 ⟨openHeap,Cache.emptyState⟩,operations⟩
private def optionalAfter : Checked 10 :=
  ⟨SourceRecursiveIntersectionThunks.advance optionalBefore.native {optionalBefore.native.machine with heap := optionalHeap},operations⟩
private def optionalControl : Control (Value Symbol Guard) := .code (.optionalBinder pair body .pure)

private theorem open_done : openBuilt = .done body openHeap := by cbv
private theorem body_available : Available openHeap body := by
  have inputs : InternedNestedProvenance.Values (empty : State Symbol Guard)
      [.reference (.intersection pair.1 pair.2)] := by
    intro value member
    cases List.mem_singleton.mp member
    apply InternedProbeProvenance.reference_available
    intro identity member
    simp only [Value.free, List.mem_singleton, reduceCtorEq] at member
  exact (InternedFreshOrdinaryFacts.build_verified openExpression _ empty InternedNestedFacts.empty_facts inputs).result _ _ open_done
private theorem optional_done : optional = .done recursiveValue optionalHeap := by
  set_option cbv.maxSteps 200000000 in cbv


private def originals : List (Value Symbol Guard) := [recursiveValue,.reference .depth]
private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0],[1]] with
  | some own => own
  | none => ⟨.empty,[]⟩
private def edits : SourceEqualityEdits.Edits EqualityNormalize.Path := .editBelow [(0,.editAt [0])]
private def shared := SourceCurrentAllocatedSharedTargetState.initial optionalAfter
  (SourceCurrentMemoMergeGraph.empty : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

/-- An actual used nested binder feeds recursive shared edits and later Local reduction without a future heap premise. -/
theorem used_binder_then_edit_local :
    openBuilt = .done body openHeap ∧
    InternedBinderProtocol.Reference.intersection pair.1 pair.2 ∈ body.free ∧
    0 < recursiveValue.depth ∧ recursiveValue.free = [] ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu pair body openHeap = .done recursiveValue optionalHeap ∧
    Trace 1 optionalControl optionalBefore (.code (.pure recursiveValue)) optionalAfter ∧
    ∀ e p h m s n,
      let edited := SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits recursiveValue shared
      SourceCurrentRequiredUnionNormal.UnionNormal edited.state.checked.native.machine.heap ∧
      ∀ g secondary r budget,
        SourceCurrentRequiredUnionNormal.UnionNormal
          (SourceCurrentAllocatedLocalWorker.reduce g secondary r e p h m s n budget
            ⟨.contradiction,.top⟩ .contradiction [.reference .depth,recursiveValue]
            edited.state.checked SourceCurrentEmptinessMemo.empty edited.state.memo).state.native.machine.heap := by
  have normal : SourceCurrentRequiredUnionNormal.UnionNormal openHeap :=
    SourceCurrentRequiredUnionNormal.build openExpression _ empty SourceCurrentRequiredUnionNormal.empty
  have one : step optionalControl optionalBefore = .yielded (.code (.pure recursiveValue)) optionalAfter := by
    have done : SourceRecursiveIntersectionMaybeMu.maybeMu pair body optionalBefore.native.machine.heap =
        .done recursiveValue optionalHeap := optional_done
    simp only [optionalControl,step,SourceRecursiveIntersectionNative.step,done,lift]
    rfl
  have actual : Trace 1 optionalControl optionalBefore (.code (.pure recursiveValue)) optionalAfter :=
    .cons _ _ _ _ _ _ 0 body_available one (.refl _ _)
  have afterNormal := SourceCurrentRequiredUnionNormalNative.trace_normal actual normal
  refine ⟨open_done,?_,?_,?_,optional_done,actual,?_⟩
  · cbv
    exact .head _
  · set_option cbv.maxSteps 200000000 in cbv
  · set_option cbv.maxSteps 200000000 in cbv
  · intro e p h m s n
    have edited := SourceCurrentUnionNormalEdits.edit record originals e p h m s n edits recursiveValue shared afterNormal
    exact ⟨edited,fun g secondary r budget => SourceCurrentUnionNormalLocalParent.reduce
      g secondary r e p h m s n budget ⟨.contradiction,.top⟩ .contradiction
      [.reference .depth,recursiveValue] _ SourceCurrentEmptinessMemo.empty _ edited⟩
end MicroCFTA.UnionLocalOptionalKernels
