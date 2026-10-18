import MicroCFTA.SourceCurrentSelectedRootOrigins
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

noncomputable section

namespace MicroCFTA.SelectedRootKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def tau : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf",.top) top [], .mk ("pair",.top) top [.var 0,.var 0]])
private def wide : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf",.top) top [], .mk ("pair",.top) top [.var 0,.var 0], .mk ("extra",.top) top []])
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [tau,wide]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance
private def before : Checked 16 := ⟨initial 16 machine, SourceEqualityConstraintMemoAllocation.empty⟩
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private def values : List (Value Symbol Guard) := [left,right]
private def fourth : SourceCurrentEmptinessMemo.Memo := SourceCurrentEmptinessMemo.empty
private def scanned := SourceCurrentAllocatedRecordScanWorker.scan 2 0 0 0 0 0 values [record,record] before fourth
private def scanResult : SourceCurrentAllocatedRecordScanWorker.Result :=
  match scanned with | .done value _ _ => value | _ => (none,[])
private def scanState := scanned.state
private def scanMemo := scanned.memo
private theorem scanned_done : scanned = .done scanResult scanState scanMemo := by
  have tag : (match scanned with | .done .. => true | _ => false) = true := by cbv
  cases found : scanned <;> simp_all only [scanResult,scanState,scanMemo,
    SourceCurrentAllocatedScanWorker.Outcome.state,SourceCurrentAllocatedScanWorker.Outcome.memo,Bool.false_eq_true]
private theorem constructed : built = .done root heap := by
  obtain ⟨value,state,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,root,heap,done,InternedNestedConstruction.Outcome.state]

private theorem witness :
    built = .done root heap ∧ record.paths = [[0],[1]] ∧ scanResult = (none,[record,record]) ∧
    scanned = .done scanResult scanState scanMemo ∧
    (match left with | .mu .. => True | _ => False) ∧
    Available heap left ∧ SourceCurrentActualRequiredRowOrigins.Root left ∧
    ∃ start finish : Checked 16, SourceCurrentAllocatedGateWorker.primary 2 values record.paths start = .done false finish := by
  have result : scanResult = (none,[record,record]) := by cbv
  have actual : SourceCurrentAllocatedRecordScanWorker.scan 2 0 0 0 0 0 values [record,record] before fourth =
      .done (none,[record,record]) scanState scanMemo := by rw [←result]; exact scanned_done
  have member : 0 :: [] ∈ record.paths := by cbv; exact List.mem_cons_self
  have found : values[0]? = some left := rfl
  have retained : record ∈ [record,record] := List.mem_cons_self
  have supported := SourceCurrentSelectedRootOrigins.selected_root actual retained member found
  have earlier := (SourceCurrentSelectedRootOrigins.selected_primary actual retained).2
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  refine ⟨constructed,?_,result,scanned_done,?_,?_,supported,earlier⟩
  · cbv
  · cbv
  · exact available.children left (by cbv; exact List.mem_cons_self)

/-- A source-built recursive slot has support from its actual retained false-primary class. -/
theorem repeated_selected_recursive :
    built = .done root heap ∧ record.paths = [[0],[1]] ∧ scanResult = (none,[record,record]) ∧
    scanned = .done scanResult scanState scanMemo ∧
    (match left with | .mu .. => True | _ => False) ∧
    Available heap left ∧ SourceCurrentActualRequiredRowOrigins.Root left ∧
    ∃ start finish : Checked 16, SourceCurrentAllocatedGateWorker.primary 2 values record.paths start = .done false finish := witness

end MicroCFTA.SelectedRootKernels
