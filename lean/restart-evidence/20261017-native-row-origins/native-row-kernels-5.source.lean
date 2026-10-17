import MicroCFTA.SourceCurrentNativeRowOrigins
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
noncomputable section
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

private theorem mu_available : Available heap mu :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed).children mu (by cbv; exact .tail _ (.head _))
private theorem row_resident : EdgeResident heap row := by
  have original := ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed).children first (by cbv; exact .head _)
  exact resident_edges heap initial_good.heap.semantic.1.normal.facts.linked first original.resident row (by cbv; exact .head _)
private theorem edge_ready : EdgeReady machine request := ⟨empty_domain machine,row_resident,row_resident⟩
private theorem mu_ready : NodeReady machine ⟨domain,mu,mu⟩ := ⟨empty_domain machine,mu_available,mu_available⟩
private theorem mu_safe : SourceRecursiveIntersectionMemo.KeySafe 8 domain mu mu := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by decide,by cbv,.mu 3,.mu 3,?_,?_,?_,?_⟩ <;> cbv

private def allocated : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨.live 0 [],.top⟩
private def selectedEdge := (lookupEdge 8 request before.native).2
private def runningEdge := (demandEdge 0 selectedEdge).2
private def edgeStarted : Checked 8 := ⟨runningEdge,operations⟩
private def checkedOps := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le allocated allocated 0 0 operations).2
private def checkedEdge : Checked 8 := ⟨runningEdge,checkedOps⟩
private def madeEdge : Checked 8 := ⟨advance runningEdge {runningEdge.machine with heap := (run (makeEdge row.entry.key.symbol top []) heap).2},checkedOps⟩
private def edgeAfter : Checked 8 := ⟨SourceRecursiveIntersectionThunks.finishEdge 0 row madeEdge.native,checkedOps⟩
private theorem cold_edge : Trace 4 (.code (requestEdge domain row row)) before (.code (.pure row)) edgeAfter := by
  have one : step (.code (requestEdge domain row row)) before = .yielded
      ((.edgeBody request .pure).bind (fun value => .finishEdge 0 value (.pure value))) edgeStarted := by cbv
  have bodyStep : step (.edgeBody request .pure) edgeStarted = .yielded
      (.code (SourceEqualityNativeCheckedCode.children domain row row allocated)) checkedEdge := by cbv
  have built : Trace 1 (.code (SourceEqualityNativeCheckedCode.children domain row row allocated)) checkedEdge
      (.code (.pure row)) madeEdge := by
    apply Trace.cons _ _ _ _ _ _ _ (SourceEqualityNativeDemandHeapPrimitives.WorkInputs.edge _ _ [] (by intro value member; cases member))
    · cbv
    · exact .refl _ _
  have bodyTrace : Trace 2 (.edgeBody request .pure) edgeStarted (.code (.pure row)) madeEdge :=
    .cons _ _ _ _ _ _ _ trivial bodyStep built
  have finish : Trace 1 (.code (.finishEdge 0 row (.pure row))) madeEdge (.code (.pure row)) edgeAfter := by
    apply Trace.cons _ _ _ _ _ _ _ ⟨request,by cbv,row_resident⟩ rfl
    exact .refl _ _
  have tail := (bodyTrace.bind (fun value => .finishEdge 0 value (.pure value))).trans finish
  exact .cons _ _ _ _ _ _ _ ⟨edge_ready,by cbv⟩ one tail
private theorem warm_edge : Trace 1 (.code (requestEdge domain row row)) edgeAfter (.code (.pure row)) edgeAfter := by
  apply Trace.cons _ _ _ _ _ _ _ ⟨edge_ready,by cbv⟩
  · cbv
  · exact .refl _ _
private def rowsCode := compileRows domain [row,row] [row]
private def rowsAfter : Checked 8 := {edgeAfter with native := advance edgeAfter.native {edgeAfter.native.machine with heap := (run (makeNode [row,row]) heap).2}}
private theorem rows_trace : Trace 6 (.code rowsCode) before (.code (.pure first)) rowsAfter := by
  have walked : SourceCurrentAllocatedNativeSemanticTraceReadback.Walk
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
      [(row,row),(row,row)] before [row,row] edgeAfter 5 :=
    .cons (row,row) _ before edgeAfter edgeAfter row [row] 4 1 cold_edge
      (.cons (row,row) [] edgeAfter edgeAfter edgeAfter row [] 1 0 warm_edge (.nil _))
  have made : Trace 1 (.code (.work (makeNode [row,row]) .pure)) edgeAfter (.code (.pure first)) rowsAfter := by
    apply Trace.cons _ _ _ _ _ _ _ (SourceEqualityNativeDemandHeapPrimitives.WorkInputs.node [row,row] (by
      intro edge member; have same : edge = row := by simpa using member; subst edge; exact row_resident))
    · cbv
    · exact .refl _ _
  have calls := walked.trace.bind (fun values => .work (makeNode values) .pure)
  have both := calls.trans made
  have same : rowsCode = ((SourceRecursiveIntersectionCode.walk
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
      [(row,row),(row,row)]).bind fun values => .work (makeNode values) .pure) := by cbv
  rw [same]
  exact both

private def muRequest : NodeRequest Symbol Guard := ⟨domain,mu,mu⟩
private def runningMu := (demandNode 0 (lookupNode 8 muRequest before.native).2).2
private def muStarted : Checked 8 := ⟨runningMu,operations⟩
private def muAfter : Checked 8 := ⟨SourceRecursiveIntersectionThunks.finishNode 0 mu runningMu,operations⟩
private theorem cold_mu : Trace 2 (.code (requestNode domain mu mu)) before (.code (.pure mu)) muAfter := by
  apply Trace.cons _ _ (.code (.finishNode 0 mu (.pure mu))) muStarted _ _ _ ⟨mu_ready,fun _ _ => mu_safe⟩
  · cbv
  · apply Trace.cons _ _ _ _ _ _ _ ⟨muRequest,by cbv,mu_available⟩ rfl
    exact .refl _ _
private theorem warm_mu : Trace 1 (.code (requestNode domain mu mu)) muAfter (.code (.pure mu)) muAfter := by
  apply Trace.cons _ _ _ _ _ _ _ ⟨mu_ready,fun _ _ => mu_safe⟩
  · cbv
  · exact .refl _ _
private def unionCode := (SourceRecursiveIntersectionCode.walk (fun member => requestNode domain member mu) [mu,mu]).bind
  (fun values => .work (makeUnion values) .pure)
private def unionAfter : Checked 8 := {muAfter with native := advance muAfter.native {muAfter.native.machine with heap := (run (makeUnion [mu,mu]) heap).2}}
private theorem union_trace : Trace 4 (.code unionCode) before (.code (.pure mu)) unionAfter := by
  have walked : SourceCurrentAllocatedNativeSemanticTraceReadback.Walk (fun member => requestNode domain member mu)
      [mu,mu] before [mu,mu] muAfter 3 :=
    .cons mu [mu] before muAfter muAfter mu [mu] 2 1 cold_mu
      (.cons mu [] muAfter muAfter muAfter mu [] 1 0 warm_mu (.nil _))
  have made : Trace 1 (.code (.work (makeUnion [mu,mu]) .pure)) muAfter (.code (.pure mu)) unionAfter := by
    apply Trace.cons _ _ _ _ _ _ _ (SourceEqualityNativeDemandHeapPrimitives.WorkInputs.union [mu,mu] (by
      intro value member; have same : value = mu := by simpa using member; subst value; exact mu_available))
    · cbv
    · exact .refl _ _
  exact (walked.trace.bind (fun values => .work (makeUnion values) .pure)).trans made

private theorem rows_proof :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (result : Node) (count : Nat),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code (compileRows domain [row,row] [row])) initialState (.code (.pure result)) finalState ∧
      (nodeEdges result).length = 1 ∧
      ∀ (outputIndex : Nat) (output : EdgeValue Symbol Guard), (nodeEdges result)[outputIndex]? = some output →
        ∃ (leftIndex rightIndex : Nat) (originalLeft originalRight : EdgeValue Symbol Guard) (current next : Checked 8) (childFuel : Nat),
          ([row,row] : List (EdgeValue Symbol Guard))[leftIndex]? = some originalLeft ∧
          ([row] : List (EdgeValue Symbol Guard))[rightIndex]? = some originalRight ∧
          originalLeft.entry.key.symbol = originalRight.entry.key.symbol ∧
          Trace childFuel (.code (requestEdge domain originalLeft originalRight)) current (.code (.pure output)) next := by
  let count := 6
  have trace := rows_trace
  obtain ⟨values,middle,walkCount,walk,fields,origins⟩ := SourceCurrentNativeRowOrigins.rows domain [row,row] [row]
    count before rowsAfter first initial_good.native initial_good.heap trace
  refine ⟨expression,before,rowsAfter,first,count,constructed,trace,by cbv,?_⟩
  intro index output selected
  obtain ⟨scheduleIndex,leftIndex,rightIndex,left,right,current,next,prefixFuel,childFuel,suffixFuel,
    found,input,leftFound,rightFound,symbol,counts,initialCalls,called,suffix⟩ := origins index output selected
  exact ⟨leftIndex,rightIndex,left,right,current,next,childFuel,leftFound,rightFound,symbol,called⟩

/-- Duplicate ordinary source rows SourceEqualityNativeDemand.execute actual edge requests before canonical output deduplication. -/
theorem ordinary_rows :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (result : Node) (count : Nat),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code (compileRows domain [row,row] [row])) initialState (.code (.pure result)) finalState ∧
      (nodeEdges result).length = 1 ∧
      ∀ (outputIndex : Nat) (output : EdgeValue Symbol Guard), (nodeEdges result)[outputIndex]? = some output →
        ∃ (leftIndex rightIndex : Nat) (originalLeft originalRight : EdgeValue Symbol Guard) (current next : Checked 8) (childFuel : Nat),
          ([row,row] : List (EdgeValue Symbol Guard))[leftIndex]? = some originalLeft ∧
          ([row] : List (EdgeValue Symbol Guard))[rightIndex]? = some originalRight ∧
          originalLeft.entry.key.symbol = originalRight.entry.key.symbol ∧
          Trace childFuel (.code (requestEdge domain originalLeft originalRight)) current (.code (.pure output)) next := rows_proof

private theorem union_proof :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (count : Nat),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code unionCode) initialState (.code (.pure mu)) finalState ∧
      finalState.native.nodes.cells 0 = some ⟨⟨domain,mu,mu⟩,.returned mu⟩ ∧
      ∀ view output, MergedFreshOrdinaryGraph.Origin view [mu] output →
        ∃ (index : Nat) (member value : Node) (current next : Checked 8) (childFuel : Nat),
          ([mu,mu] : List Node)[index]? = some member ∧
          Trace childFuel (.code (requestNode domain member mu)) current (.code (.pure value)) next ∧
          MergedFreshOrdinaryGraph.Origin view [value] output := by
  let count := 4
  have trace := union_trace
  have original : SourceRecursiveIntersectionInputView.Original mu := by
    have coherent := initial_good.heap.semantic.1.normal.facts.coherent
    have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
    have muAvailable := available.children mu (by cbv; exact .tail _ (.head _))
    exact SourceRecursiveIntersectionOriginalOutput.closed_original mu heap coherent muAvailable (by cbv)
  obtain ⟨values,middle,walkCount,walk,origins⟩ := SourceCurrentNativeRowOrigins.union domain [mu,mu] mu true count before unionAfter mu
    initial_good.native initial_good.heap (by
      intro member included
      have same : member = mu := by simpa using included
      subst member
      exact ⟨original,original⟩) trace
  refine ⟨expression,before,unionAfter,count,constructed,trace,by cbv,?_⟩
  intro view output occurrence
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,found,selected,counts,initialCalls,called,suffix,origin⟩ :=
    origins view output (occurrence)
  exact ⟨index,member,value,current,next,childFuel,found,called,origin⟩

/-- A source-built productive Mu is returned by a cold member call and an exact warm duplicate call. -/
theorem union_members :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (count : Nat),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace count (.code unionCode) initialState (.code (.pure mu)) finalState ∧
      finalState.native.nodes.cells 0 = some ⟨⟨domain,mu,mu⟩,.returned mu⟩ ∧
      ∀ view output, MergedFreshOrdinaryGraph.Origin view [mu] output →
        ∃ (index : Nat) (member value : Node) (current next : Checked 8) (childFuel : Nat),
          ([mu,mu] : List Node)[index]? = some member ∧
          Trace childFuel (.code (requestNode domain member mu)) current (.code (.pure value)) next ∧
          MergedFreshOrdinaryGraph.Origin view [value] output := union_proof
end MicroCFTA.NativeRowOriginKernels
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeRowOriginKernels.ordinary_rows
#print MicroCFTA.NativeRowOriginKernels.ordinary_rows
#print axioms MicroCFTA.NativeRowOriginKernels.ordinary_rows
#check @MicroCFTA.NativeRowOriginKernels.union_members
#print MicroCFTA.NativeRowOriginKernels.union_members
#print axioms MicroCFTA.NativeRowOriginKernels.union_members
