import MicroCFTA.SourceCurrentNativeRowOrigins
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
namespace MicroCFTA.NativeRowOriginKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentNativeRowOrigins
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def top : Guard := SourceEqualityConstraintConstructors.top
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) top []]
private def productive : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf",.top) top [], .mk ("step",.top) top [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) top [leaf,productive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem constructed : built = .done root heap := by cbv
private def first : Node := ((children root)[0]?).getD .empty
private def mu : Node := ((children root)[1]?).getD .empty
private def row : EdgeValue Symbol Guard := match first with
  | .node _ (edge :: _) _ _ => edge
  | _ => (run (makeEdge ("fallback",.top) top []) empty).1
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 8 := ⟨initial 8 machine,operations⟩
private def domain := IntersectionEmptyDomain.emptyDomain
private def request : EdgeRequest Symbol Guard := ⟨domain,row,row⟩
private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression,leaf,productive,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built,heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts,Cache.empty_valid⟩,semantic.ready,loaded.1,?_⟩
  intro key edge found
  have same := guarded key edge found
  rw [same]
  exact loaded.2.2

private theorem trace_of_done {A : Type} (fuel : Nat) (control : Control A) (before after : Checked 8) (value : A)
    (done : execute fuel control before = .done value after)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control before) :
    ∃ count, Trace count control before (.code (.pure value)) after := by
  induction fuel generalizing control before with
  | zero => cases done
  | succ fuel ih =>
    cases one : step control before with
    | done output final =>
      have same := Outcome.done.inj (by simpa only [execute,one] using done)
      obtain ⟨rfl,rfl⟩ := same
      obtain ⟨rfl,rfl⟩ := (step_done_iff control before after value).mp one
      exact ⟨0,.refl _ _⟩
    | yielded next middle =>
      obtain ⟨count,tail⟩ := ih next middle
        (by simpa only [execute,one] using done)
        (by simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough,one] using inputs.2)
      exact ⟨count+1,.cons _ _ _ _ _ _ _ inputs.1 one tail⟩
    | failed | constraintError | blocked => simp only [execute,one] at done; cases done

private def rowsCode := compileRows domain [row,row] [row]
private def rowsRun := execute 16 (.code rowsCode) before
private def rowsResult : Node := match rowsRun with | .done value _ => value | _ => .empty
private def rowsAfter : Checked 8 := rowsRun.state
private theorem rows_done : rowsRun = .done rowsResult rowsAfter := by cbv
private theorem rows_inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 16 (.code rowsCode) before := by
  cbv

private def unionCode := (SourceRecursiveIntersectionCode.walk (fun member => requestNode domain member mu) [mu,mu]).bind
  (fun values => .work (makeUnion values) .pure)
private def unionRun := execute 16 (.code unionCode) before
private def unionResult : Node := match unionRun with | .done value _ => value | _ => .empty
private def unionAfter : Checked 8 := unionRun.state
private theorem union_done : unionRun = .done unionResult unionAfter := by cbv
private theorem union_inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 16 (.code unionCode) before := by
  cbv

private theorem rows_proof :
    ∃ program initialState finalState result count,
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code (compileRows domain [row,row] [row])) initialState (.code (.pure result)) finalState ∧
      (nodeEdges result).length = 1 ∧
      ∀ outputIndex output, (nodeEdges result)[outputIndex]? = some output →
        ∃ leftIndex rightIndex originalLeft originalRight current next childFuel,
          ([row,row] : List (EdgeValue Symbol Guard))[leftIndex]? = some originalLeft ∧
          ([row] : List (EdgeValue Symbol Guard))[rightIndex]? = some originalRight ∧
          originalLeft.entry.key.symbol = originalRight.entry.key.symbol ∧
          Trace childFuel (.code (requestEdge domain originalLeft originalRight)) current (.code (.pure output)) next := by
  obtain ⟨count,trace⟩ := trace_of_done 16 (.code rowsCode) before rowsAfter rowsResult rows_done rows_inputs
  obtain ⟨values,middle,walkCount,walk,fields,origins⟩ := SourceCurrentNativeRowOrigins.rows domain [row,row] [row]
    count before rowsAfter rowsResult initial_good.native initial_good.heap trace
  refine ⟨expression,before,rowsAfter,rowsResult,count,constructed,trace,by cbv,?_⟩
  intro index output selected
  obtain ⟨scheduleIndex,leftIndex,rightIndex,left,right,current,next,prefixFuel,childFuel,suffixFuel,
    found,input,leftFound,rightFound,symbol,counts,initialCalls,called,suffix⟩ := origins index output selected
  exact ⟨leftIndex,rightIndex,left,right,current,next,childFuel,leftFound,rightFound,symbol,called⟩

/-- Duplicate ordinary source rows execute actual edge requests before canonical output deduplication. -/
theorem ordinary_rows :
    ∃ program initialState finalState result count,
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code (compileRows domain [row,row] [row])) initialState (.code (.pure result)) finalState ∧
      (nodeEdges result).length = 1 ∧
      ∀ outputIndex output, (nodeEdges result)[outputIndex]? = some output →
        ∃ leftIndex rightIndex originalLeft originalRight current next childFuel,
          ([row,row] : List (EdgeValue Symbol Guard))[leftIndex]? = some originalLeft ∧
          ([row] : List (EdgeValue Symbol Guard))[rightIndex]? = some originalRight ∧
          originalLeft.entry.key.symbol = originalRight.entry.key.symbol ∧
          Trace childFuel (.code (requestEdge domain originalLeft originalRight)) current (.code (.pure output)) next := rows_proof

private theorem union_proof :
    ∃ program initialState finalState count,
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code unionCode) initialState (.code (.pure mu)) finalState ∧
      finalState.native.nodes.cells 0 = some ⟨⟨domain,mu,mu⟩,.returned mu⟩ ∧
      ∀ view output, MergedFreshOrdinaryGraph.Origin view [mu] output →
        ∃ index member value current next childFuel,
          ([mu,mu] : List Node)[index]? = some member ∧
          Trace childFuel (.code (requestNode domain member mu)) current (.code (.pure value)) next ∧
          MergedFreshOrdinaryGraph.Origin view [value] output := by
  have same : unionResult = mu := by cbv
  obtain ⟨count,trace⟩ := trace_of_done 16 (.code unionCode) before unionAfter unionResult union_done union_inputs
  have original : SourceRecursiveIntersectionInputView.Original mu := by
    have coherent := initial_good.heap.semantic.1.normal.facts.coherent
    have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
    have muAvailable := available.children mu (by cbv; exact .tail _ (.head _))
    exact SourceRecursiveIntersectionOriginalOutput.closed_original mu heap coherent muAvailable (by cbv)
  obtain ⟨values,middle,walkCount,walk,origins⟩ := SourceCurrentNativeRowOrigins.union domain [mu,mu] mu true count before unionAfter unionResult
    initial_good.native initial_good.heap (by intro member included; rcases List.mem_cons.mp included with rfl | included
                                           · exact ⟨original,original⟩
                                           · cases List.mem_singleton.mp included; exact ⟨original,original⟩) trace
  refine ⟨expression,before,unionAfter,count,constructed,by simpa only [same] using trace,by cbv,?_⟩
  intro view output occurrence
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,found,selected,counts,initialCalls,called,suffix,origin⟩ :=
    origins view output (by simpa only [same] using occurrence)
  exact ⟨index,member,value,current,next,childFuel,found,called,origin⟩

/-- A source-built productive Mu is returned by a cold member call and an exact warm duplicate call. -/
theorem union_members :
    ∃ program initialState finalState count,
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code unionCode) initialState (.code (.pure mu)) finalState ∧
      finalState.native.nodes.cells 0 = some ⟨⟨domain,mu,mu⟩,.returned mu⟩ ∧
      ∀ view output, MergedFreshOrdinaryGraph.Origin view [mu] output →
        ∃ index member value current next childFuel,
          ([mu,mu] : List Node)[index]? = some member ∧
          Trace childFuel (.code (requestNode domain member mu)) current (.code (.pure value)) next ∧
          MergedFreshOrdinaryGraph.Origin view [value] output := union_proof
end MicroCFTA.NativeRowOriginKernels
#check @MicroCFTA.NativeRowOriginKernels.ordinary_rows
#print MicroCFTA.NativeRowOriginKernels.ordinary_rows
#print axioms MicroCFTA.NativeRowOriginKernels.ordinary_rows
#check @MicroCFTA.NativeRowOriginKernels.union_members
#print MicroCFTA.NativeRowOriginKernels.union_members
#print axioms MicroCFTA.NativeRowOriginKernels.union_members
