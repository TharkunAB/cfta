import MicroCFTA.SourceCurrentNativeClosedGuardAlphabet
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
set_option linter.all true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.ClosedAlphabetCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentNativeClosedGuardAlphabet
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def first : Guard := ⟨some [],.or [.top,.top]⟩
private def second : Guard := ⟨some [],.not (.not .top)⟩
private def symbol : Symbol := ("unit",.top)
private def expression : Syntax Symbol Guard := .node [.mk symbol first [],.mk symbol second []]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct first.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok result => result | .error _ => .contradiction
private def before : Checked 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocated.2⟩
private def left := (run (makeEdge symbol first []) heap).1
private def right := (run (makeEdge symbol second []) heap).1
private def request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control (EdgeValue Symbol Guard) := .edgeBody request .pure
private def literals := SourceEqualityConstraintOrigins.guards expression
private def alphabet := originalAlphabet literals

private theorem constructed : built = .done value heap := by cbv
private theorem allocation_history : SourceEqualityOriginalAllocationHistory.History
    Cache.emptyState allocated.2 [first,second] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [first] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
      (show SourceEqualityConstraintAllocation.construct first.equalities Cache.emptyState = (.ok field,allocated.2) by cbv)
  simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    one SourceEqualityGuardReadback.empty_cached
    (show SourceEqualityConstraintAllocation.construct second.equalities allocated.2 = (.ok field,allocated.2) by cbv)

private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready before :=
  (SourceCurrentConjunctionClassHistoryEntry.constructed 8 allocation_history Cache.empty_valid expression
    (by intro guard member; exact member) value heap constructed).1
private theorem normalized : ∀ guard ∈ literals, SourceEqualityGuardReadback.Cached guard.equalities := by
  intro guard member
  change guard ∈ [first,second] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact SourceEqualityGuardReadback.empty_cached
  · cases List.mem_singleton.mp member
    exact SourceEqualityGuardReadback.empty_cached
private theorem initial_origins : SourceEqualityAnnotationHeap.Heap
    (SourceEqualityConstraintOrigins.Derived literals SourceEqualityConstraintConstructors.top
      SourceEqualityPCSNativeEdge.conjoin) heap :=
  SourceEqualityConstraintOrigins.constructed _ _ expression value heap constructed
private theorem left_member : left ∈ nodeEdges value := by cbv; exact .head _
private theorem right_member : right ∈ nodeEdges value := by cbv; exact .tail _ (.head _)
private theorem input_available : Available heap value :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result value heap constructed
private theorem resident_left : EdgeResident heap left :=
  resident_edges heap initial_ready.good.native.machine.1.linked value input_available.resident left left_member
private theorem resident_right : EdgeResident heap right :=
  resident_edges heap initial_ready.good.native.machine.1.linked value input_available.resident right right_member
private theorem request_ready : EdgeReady before.native.machine request :=
  ⟨empty_domain _,resident_left,resident_right⟩

private def step1 := SourceEqualityNativeDemand.step control before
private def middle := step1.state
private def next : Control (EdgeValue Symbol Guard) := match step1 with
  | .yielded rest _ => rest | _ => .code (.pure left)
private def step2 := SourceEqualityNativeDemand.step next middle
private def after := step2.state
private def last : Control (EdgeValue Symbol Guard) := match step2 with
  | .yielded rest _ => rest | _ => .code (.pure left)
private def result := match last with | .code (.pure edge) => edge | _ => left

private theorem step1_yielded : SourceEqualityNativeDemand.step control before = .yielded next middle := by cbv
private theorem step2_yielded : SourceEqualityNativeDemand.step next middle = .yielded last after := by cbv
private theorem next_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs next middle := by
  change SourceEqualityNativeDemandHeapPrimitives.WorkInputs middle.native.machine.heap
    (makeEdge symbol (SourceEqualityPCSNativeEdge.conjoin first second) [])
  exact .edge _ _ _ (by intro item member; cases member)
private theorem trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace 2 control before last after :=
  .cons _ _ _ _ _ _ _ trivial step1_yielded (.cons _ _ _ _ _ _ _ next_inputs step2_yielded (.refl _ _))

private theorem witness :
    built = .done value heap ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace 2 control before (.code (.pure result)) after ∧
    result.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin first second ∧
    result.entry.key.constraint ≠ first ∧ result.entry.key.constraint ≠ second ∧
    EdgeResident after.native.machine.heap result ∧
    result.entry.key.constraint ∈ alphabet ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.native.machine.heap ∧
    SourceCurrentNativeGuardStep.Fields alphabet (.code (.pure result)) := by
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before := ⟨request_ready,fun _ => trivial⟩
  have retained := original_retained literals normalized trace initial_ready.good fields initial_origins (fun _ => trivial)
  have shape : last = .code (.pure result) := by cbv
  have resident : EdgeResident after.native.machine.heap result := by cbv
  have member := retained.1 result.entry.key result resident
  refine ⟨constructed,initial_ready.good,shape ▸ trace,?_,?_,?_,resident,member,retained.1,?_⟩
  · cbv
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · simpa only [shape] using retained.2

/-- Actual source rows emit a new joined guard and retain the fixed finite carrier through both instructions. -/
theorem source_conjoin_fixed_carrier :
    built = .done value heap ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace 2 control before (.code (.pure result)) after ∧
    result.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin first second ∧
    result.entry.key.constraint ≠ first ∧ result.entry.key.constraint ≠ second ∧
    EdgeResident after.native.machine.heap result ∧
    result.entry.key.constraint ∈ alphabet ∧
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.native.machine.heap ∧
    SourceCurrentNativeGuardStep.Fields alphabet (.code (.pure result)) := witness

end MicroCFTA.ClosedAlphabetCheck
