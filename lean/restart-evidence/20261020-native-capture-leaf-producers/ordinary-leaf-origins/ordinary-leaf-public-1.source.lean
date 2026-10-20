import MicroCFTA.SourceCurrentNativeActiveRowOrigins
import MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut

/-!
# Indexed leaves of actual ordinary native results

The leaf traversal stops at a closed result. An open ordinary result keeps
its exact row, child and inner leaf positions. The actual prefix supplies
that child's indexed source rows, checked call and same-reader writer.
-/
namespace MicroCFTA.SourceCurrentNativeOrdinaryLeafOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedStoredSubstitution (leaves manyLeaves edgeLeaves)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects Walk)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentNativeForwardLineage (Forwarded)
open SourceRecursiveIntersectionControl (decision)
open SourceCurrentIndexedFirstOrdinaryCut (Cut)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

private theorem flat_lookup (f : α → List β) (values : List α) (index : Nat) (value : β)
    (found : (values.flatMap f)[index]? = some value) :
    ∃ outer selected inner,
      values[outer]? = some selected ∧ (f selected)[inner]? = some value ∧
      index = ((values.take outer).flatMap f).length + inner := by
  induction values generalizing index with
  | nil => simp only [List.flatMap_nil,List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      simp only [List.flatMap_cons] at found
      by_cases short : index < (f first).length
      · rw [List.getElem?_append_left short] at found
        exact ⟨0,first,index,rfl,found,by simp only [List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add]⟩
      · have long : (f first).length ≤ index := by omega
        rw [List.getElem?_append_right long] at found
        obtain ⟨outer,selected,inner,source,inside,offset⟩ := ih (index - (f first).length) found
        refine ⟨outer + 1,selected,inner,source,inside,?_⟩
        simp only [List.take_succ_cons,List.flatMap_cons,List.length_append]
        omega

private theorem many_flat (values : List (Value Symbol Guard)) :
    manyLeaves values = values.flatMap leaves := by
  induction values with
  | nil => simp only [manyLeaves,List.flatMap_nil]
  | cons first rest ih => simp only [manyLeaves,List.flatMap_cons,ih]

private theorem edges_flat (rows : List (EdgeValue Symbol Guard)) :
    edgeLeaves rows = rows.flatMap (fun row => manyLeaves row.children) := by
  induction rows with
  | nil => simp only [edgeLeaves,List.flatMap_nil]
  | cons row rest ih =>
      cases row
      simp only [edgeLeaves,EdgeValue.children,List.flatMap_cons,ih]

private theorem ordinary_payload (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    SourceRecursiveIntersectionControl.payload request.left request.right = .ordinary := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact selected

private theorem ordinary_code [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    compileNode request = compileRows request.domain (nodeEdges request.left) (nodeEdges request.right) := by
  have payload := ordinary_payload request selected
  cases left : request.left <;> cases right : request.right <;>
    simp only [left,right,SourceRecursiveIntersectionControl.payload] at payload <;> try cases payload
  unfold compileNode
  simp only [selected]
  rw [left,right]
  rfl


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem walk_edges (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    {inputs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard)} {before after : Checked width}
    {values : List (EdgeValue Symbol Guard)} {fuel : Nat}
    (walked : Walk (fun pair => requestEdge domain pair.1 pair.2) inputs before values after fuel)
    (good : Good before) : InternedNestedProvenance.Edges after.native.machine.heap values := by
  induction walked with
  | nil => intro edge member; cases member
  | cons pair pairs before current after edge edges firstFuel restFuel called tail ih =>
    have firstFacts := effects called good (by intro value; trivial)
    have firstEdge := SourceCurrentAllocatedNativeRequestResults.edge_result firstFuel
      ⟨domain,pair.1,pair.2⟩ before current edge good.native called
    have remaining := ih firstFacts.1
    have tailFields := SourceCurrentAllocatedNativeCodeFields.fields_walk current.operations
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
      pairs (by intro pair included value; trivial)
    have finalFacts := effects tail.trace firstFacts.1 tailFields
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge_grows _ _ finalFacts.2.2.1.growth _ firstEdge
    · exact remaining value member

private theorem ordinary_result {before after : Checked width}
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after) :
    SourceEqualityRequiredCache.Ordinary result := by
  obtain ⟨inner,outer,values,middle,_,first,last⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard =>
      requestEdge domain pair.1 pair.2) (pairs left right))) (fun values => .work (makeNode values) .pure)
    before after result actual
  have walked := SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback _ _ inner _ _ _ first
  have resident := walk_edges domain walked good
  have walkFields := SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
    (pairs left right) (by intro pair included value; trivial)
  have current := effects first good walkFields
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  rw [observed.1]
  exact SourceEqualityRequiredCache.node_ordinary values middle.native.machine.heap
    current.1.heap.semantic.1.normal.facts resident

/-- An actual indexed ordinary leaf keeps its whole closed writer or its exact checked child producer. -/
theorem leaf {A : Type} (control final : Control A) (initial reader : Checked width) (count : Nat)
    (clean : Clean control) (good : Good initial) (fields : Fields control initial)
    (history : History initial) (actual : Trace count control initial final reader)
    (request : NodeRequest Symbol Guard) (result : Node) (handle : Nat)
    (cell : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (ordinary : decision request.domain.key request.left request.right = .ordinary)
    (leafIndex : Nat) (selectedLeaf : Node) (found : (leaves result)[leafIndex]? = some selectedLeaf) :
    (leafIndex = 0 ∧ selectedLeaf = result ∧ result.free = [] ∧
      SourceCurrentNativeWriterReadyRetention.Written handle request result reader.native) ∨
    ∃ (outputIndex : Nat) (row : EdgeValue Symbol Guard) (childIndex : Nat) (child : Node) (inner : Nat)
        (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (edgeHandle : Nat)
        (leftChild rightChild : Node) (before after : Checked width) (fuel childHandle : Nat),
      result.free ≠ [] ∧
      (nodeEdges result)[outputIndex]? = some row ∧ row.children[childIndex]? = some child ∧
      (leaves child)[inner]? = some selectedLeaf ∧
      leafIndex = (edgeLeaves ((nodeEdges result).take outputIndex)).length +
        (manyLeaves (row.children.take childIndex)).length + inner ∧
      Cut result leafIndex selectedLeaf row childIndex child inner ∧
      (nodeEdges request.left)[leftIndex]? = some leftRow ∧
      (nodeEdges request.right)[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      SourceCurrentNativeEdgeWriterRetention.Written edgeHandle ⟨request.domain,leftRow,rightRow⟩ row reader.native ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[childIndex]? = some leftChild ∧ rightRow.children[childIndex]? = some rightChild ∧
      Good before ∧ Good after ∧ Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧
      Trace fuel (.code (requestNode request.domain leftChild rightChild)) before (.code (.pure child)) after ∧
      Retained after.native reader.native ∧
      Forwarded reader ⟨request.domain,leftChild,rightChild⟩ before after child ∧
      reader.native.nodes.cells childHandle = some ⟨⟨request.domain,leftChild,rightChild⟩,.returned child⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written childHandle ⟨request.domain,leftChild,rightChild⟩ child reader.native := by
  have maps := SourceCurrentNativePrefixWriterMaps.prefix control initial reader final count clean good fields history actual
  have written := maps.1 handle request result cell
  have ordinaryResult : SourceEqualityRequiredCache.Ordinary result := by
    obtain ⟨before,after,fuel,ready,_,_,body,_,_,_,_,_⟩ := written
    exact ordinary_result request.domain (nodeEdges request.left) (nodeEdges request.right)
      fuel result ready ((ordinary_code request ordinary) ▸ body)
  by_cases closed : result.free = []
  · have rootFound : ([result] : List Node)[leafIndex]? = some selectedLeaf := by
      simpa only [leaves.eq_def,closed,List.isEmpty_nil,↓reduceIte] using found
    cases leafIndex with
    | zero => exact .inl ⟨rfl,(Option.some.inj rootFound).symm,closed,written⟩
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at rootFound; cases rootFound
  · cases result with
    | empty => exact False.elim (closed rfl)
    | reference | union | mu => cases ordinaryResult
    | node entry rows depth free =>
      change free ≠ [] at closed
      have rawLeaves : leaves (.node entry rows depth free : Node) = edgeLeaves rows := by
        rw [leaves.eq_def]
        simp only [Value.free,List.isEmpty_eq_false_iff.mpr closed,Bool.false_eq_true,↓reduceIte]
      rw [rawLeaves,edges_flat] at found
      obtain ⟨outputIndex,row,rowInner,selected,inside,rowOffset⟩ :=
        flat_lookup (fun edge : EdgeValue Symbol Guard => manyLeaves edge.children) rows leafIndex selectedLeaf found
      rw [many_flat] at inside
      obtain ⟨childIndex,child,inner,childSelected,leafSelected,childOffset⟩ :=
        flat_lookup leaves row.children rowInner selectedLeaf inside
      have offset : leafIndex = (edgeLeaves (rows.take outputIndex)).length +
          (manyLeaves (row.children.take childIndex)).length + inner := by
        rw [edges_flat,many_flat]
        omega
      have cut : Cut (.node entry rows depth free) leafIndex selectedLeaf row childIndex child inner :=
        .node closed selected childSelected leafSelected offset
      obtain ⟨leftIndex,rightIndex,leftRow,rightRow,edgeHandle,leftChild,rightChild,before,after,
        fuel,childHandle,leftFound,rightFound,symbols,edgeWriter,symbol,guard,leftSelected,rightSelected,
        beforeGood,afterGood,beforeGrowth,afterGrowth,called,retained,forwarded,childCell,childWriter⟩ :=
        SourceCurrentNativeActiveRowOrigins.child control final initial reader count clean good fields history actual
          request (.node entry rows depth free) handle cell ordinary outputIndex row selected childIndex child childSelected
      exact .inr ⟨outputIndex,row,childIndex,child,inner,leftIndex,rightIndex,leftRow,rightRow,edgeHandle,
        leftChild,rightChild,before,after,fuel,childHandle,closed,selected,childSelected,leafSelected,offset,cut,
        leftFound,rightFound,symbols,edgeWriter,symbol,guard,leftSelected,rightSelected,
        beforeGood,afterGood,beforeGrowth,afterGrowth,called,retained,forwarded,childCell,childWriter⟩

end MicroCFTA.SourceCurrentNativeOrdinaryLeafOrigins

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
#check @MicroCFTA.SourceCurrentNativeOrdinaryLeafOrigins.leaf
#print MicroCFTA.SourceCurrentNativeOrdinaryLeafOrigins.leaf
#print axioms MicroCFTA.SourceCurrentNativeOrdinaryLeafOrigins.leaf
