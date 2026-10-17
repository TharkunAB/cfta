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

namespace MicroCFTA.RequiredUnionNativeKernels
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
private def base : Syntax Symbol Guard := .node [.mk ("base", .top) top []]
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  .node [.mk ("step", .top) top [base]],
  .node [.mk ("step", .top) top [base], .mk ("other", .top) top []],
  .binder false (.union [base,.var 0])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 10 := ⟨initial 10 machine, operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, base, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  have same := guarded key row found
  rw [same]
  exact loaded.2.2

private theorem originals : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact available.children left (by cbv; exact .head _)
  · exact available.children right (by cbv; exact .tail _ (.head _))

private theorem node_ready : NodeReady machine request := ⟨empty_domain machine, originals.1, originals.2⟩

private theorem shapes :
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape 2 1 left ∧
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape 2 1 right := by
  cbv

private theorem heights : max (MergedOrdinaryHeight.height left) (MergedOrdinaryHeight.height right) ≤ 2 := by cbv

private theorem original_key : ∃ key,
    SourceRecursiveIntersectionMemo.requestKey 10 request.domain request.left request.right = some key := by
  have present : (SourceRecursiveIntersectionMemo.requestKey 10 request.domain request.left request.right).isSome = true := by cbv
  cases found : SourceRecursiveIntersectionMemo.requestKey 10 request.domain request.left request.right with
  | none => rw [found] at present; cases present
  | some key => exact ⟨key, rfl⟩

private def nodeControl : Control (Value Symbol Guard) := .code (requestNode request.domain left right)


private theorem source_normal : SourceCurrentRequiredUnionNormal.UnionNormal heap :=
  SourceCurrentRequiredUnionNormal.source expression

/-- Own cold compilation and warm publication retain union records before actual selected Required work. -/
theorem cold_native_then_required :
    built = .done root heap ∧ left ≠ right ∧ SourceCurrentRequiredUnionNormal.UnionNormal heap ∧
    ∃ fuel value after key handle required final,
      Trace fuel nodeControl before (.code (.pure value)) after ∧
      SourceCurrentRequiredUnionNormal.UnionNormal after.native.machine.heap ∧
      after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request,.returned value⟩ ∧
      execute 2 nodeControl after = .done value after ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun worker reader => SourceEqualityRequiredExecution.requireAll worker reader [[0,0]]
          [value,.reference .depth] after.native.machine.heap) [required,.reference .depth] final ∧
      SourceCurrentRequiredUnionNormal.UnionNormal final ∧
      ∀ worker reader, SourceCurrentRequiredUnionNormalRead.StoppedNormal
        (SourceEqualityRequiredExecution.requireAll worker reader [[0,0]]
          [value,.reference .depth] after.native.machine.heap) := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  obtain ⟨fuel,value,after,receipt,_idle,afterSemantic,_stored,_output,_shape,_height,_rightHeight,closed,_capacity,_nodes,_edges⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOutputFinite.cold 8 2 1 2 (fun _ _ => true)
      before initial_good semantic rfl left right originals.1 originals.2 shapes.1 shapes.2 heights
      (by cbv) (by cbv)
  have afterNormal := SourceCurrentRequiredUnionNormalNative.trace_normal receipt.trace source_normal
  obtain ⟨key,requested⟩ := original_key
  obtain ⟨⟨handle,published,returned⟩,repeated⟩ :=
    SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace fuel request before after value initial_good.native key requested receipt.trace
  let needed : SourceEqualityNeeded.Needed := .node [(0,.node [])]
  obtain ⟨required,final,actual,_kept,_available,_closed,_stable⟩ :=
    SourceEqualityRequiredExecution.complete needed value after.native.machine.heap afterSemantic.ready receipt.result closed
  have children : SourceEqualityRequiredGraph.RequireChildren [(0,needed)] 0
      [value,.reference .depth] after.native.machine.heap [required,.reference .depth] final :=
    .selected 0 rfl actual (.unselected 1 rfl .nil)
  have compiled : SourceEqualityNeeded.build [[0,0]] = .node [(0,needed)] := by cbv
  have stable : SourceEqualityRequiredWorkerComplete.StableRun
      (fun worker reader => SourceEqualityRequiredExecution.requireAll worker reader [[0,0]]
        [value,.reference .depth] after.native.machine.heap) [required,.reference .depth] final := by
    simpa only [SourceEqualityRequiredExecution.requireAll,compiled] using
      SourceEqualityRequiredWorkerComplete.children_stable children
  refine ⟨constructed,?_,source_normal,fuel,value,after,key,handle,required,final,receipt.trace,afterNormal,
    published,returned,repeated,stable,SourceCurrentRequiredUnionNormalRead.required_node actual afterNormal,?_⟩
  · intro same
    have refs := congrArg Value.referenceOf same
    cbv at refs
    cases refs
  · intro worker reader
    exact SourceCurrentRequiredUnionNormalRead.requireAll worker reader [[0,0]] _ _ afterNormal

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
    cases member
  exact (InternedFreshOrdinaryFacts.build_verified openExpression _ empty InternedNestedFacts.empty_facts inputs).result _ _ open_done
private theorem optional_done : optional = .done recursiveValue optionalHeap := by
  set_option cbv.maxSteps 200000000 in cbv

/-- Actual used optional binding on an open nested-Mu source retains normality through its checked yield and every later Head/Required outcome. -/
theorem optional_nested_then_open_reads :
    openBuilt = .done body openHeap ∧
    InternedBinderProtocol.Reference.intersection pair.1 pair.2 ∈ body.free ∧
    0 < recursiveValue.depth ∧ recursiveValue.free = [] ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu pair body openHeap = .done recursiveValue optionalHeap ∧
    Trace 1 optionalControl optionalBefore (.code (.pure recursiveValue)) optionalAfter ∧
    SourceCurrentRequiredUnionNormal.UnionNormal optionalAfter.native.machine.heap ∧
    ∀ worker reader,
      SourceCurrentRequiredUnionNormalRead.StoppedNormal
        (SourceEqualityRequiredWorker.head reader recursiveValue optionalAfter.native.machine.heap) ∧
      SourceCurrentRequiredUnionNormalRead.StoppedNormal
        (SourceEqualityRequiredExecution.requireAll worker reader [[0,0],[2,0]]
          [recursiveValue,.reference .depth,.reference .depth] optionalAfter.native.machine.heap) := by
  have normal : SourceCurrentRequiredUnionNormal.UnionNormal openHeap :=
    SourceCurrentRequiredUnionNormal.build openExpression _ empty SourceCurrentRequiredUnionNormal.empty
  have one : step optionalControl optionalBefore = .yielded (.code (.pure recursiveValue)) optionalAfter := by
    simp only [optionalControl,step,SourceRecursiveIntersectionNative.step,optionalBefore,optionalAfter,optional,
      optional_done,lift]
  have actual : Trace 1 optionalControl optionalBefore (.code (.pure recursiveValue)) optionalAfter :=
    .cons _ _ _ _ _ _ 0 body_available one (.refl _ _)
  have afterNormal := SourceCurrentRequiredUnionNormalNative.trace_normal actual normal
  refine ⟨open_done,?_,?_,?_,optional_done,actual,afterNormal,?_⟩
  · cbv
  · set_option cbv.maxSteps 200000000 in cbv
  · set_option cbv.maxSteps 200000000 in cbv
  · intro worker reader
    exact ⟨SourceCurrentRequiredUnionNormalRead.head reader _ _ afterNormal,
      SourceCurrentRequiredUnionNormalRead.requireAll worker reader _ _ _ afterNormal⟩
end MicroCFTA.RequiredUnionNativeKernels

#check @MicroCFTA.RequiredUnionNativeKernels.cold_native_then_required
#print axioms MicroCFTA.RequiredUnionNativeKernels.cold_native_then_required
#check @MicroCFTA.RequiredUnionNativeKernels.optional_nested_then_open_reads
#print axioms MicroCFTA.RequiredUnionNativeKernels.optional_nested_then_open_reads
