import MicroCFTA.SourceCurrentNativeOriginBranches
import MicroCFTA.SourceCurrentNativeNodeRowLineage

/-!
# Captured native calls at a separate physical origin view

The checked reader retains actual native cells and their earlier writers.
The physical view supplies the selected row origin. These states can
differ. No native memo history is assigned to the physical view.
Ordinary child calls retain both strict operand-child mass bounds.
Union and reference calls retain the same complete row at the given view.
A Mu body uses the chosen captured writer. Its stored unfolding uses the
given physical view. These two executions are not identified.
-/
namespace MicroCFTA.SourceCurrentNativeOriginViewBranches
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk bind_inverse effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeQueryRowOrigins (Route)
open SourceCurrentNativeOriginExposure (Writer Unfold)
open SourceCurrentNativeForwardLineage (Forwarded)
open SourceEqualityNativeDemandMemo (Retained)
open MergedFreshOrdinaryGraph (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}
private theorem ordinary_payload (request : NodeRequest Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary) :
    SourceRecursiveIntersectionControl.payload request.left request.right = .ordinary := by
  unfold SourceRecursiveIntersectionControl.decision at selected
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

private theorem ordinary_origin [DecidableEq (EdgeKey Symbol Guard)] {result : Value Symbol Guard} (ordinary : SourceEqualityRequiredCache.Ordinary result)
    (view : Heap) (row : EdgeValue Symbol Guard) (origin : Origin view [result] row) :
    ∃ index : Nat, (nodeEdges result)[index]? = some row := by
  cases result with
  | empty => exact (MergedFreshOrdinaryGraph.origin_empty view row origin).elim
  | node entry edges depth free =>
    exact List.mem_iff_getElem?.mp ((MergedFreshOrdinaryGraph.origin_node view entry edges depth free row).mp origin)
  | reference | union | mu => cases ordinary

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A captured returned cell supplies its writer while Mu exposure stays at the separate view. -/
theorem returned {reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (present : ∃ handle, reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (view : Heap) (valid : InternedConstructorTemplates.Valid view)
    (row : EdgeValue Symbol Guard) (origin : Origin view [result] row) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
      (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
      Writer reader handle terminal result ∧
      ∀ entry body depth ordinary, result = .mu entry body depth ordinary →
        Unfold view entry body depth ordinary row := by
  obtain ⟨terminal,handle,route,cell,writer,notSwap,notReset,first,second⟩ :=
    SourceCurrentNativeOpenQueryForwarding.normalize history request result left right present
  obtain ⟨before,after,fuel,good,ready,owner,actual,kept,finish,firstGrowth,lastGrowth,retained⟩ := writer
  refine ⟨terminal,handle,route,cell,notSwap,notReset,first,second,
    ⟨before,after,fuel,good,ready,owner,actual,kept,finish,firstGrowth,lastGrowth,retained,?_⟩,?_⟩
  · intro branch
    have compiled : compileNode terminal = compileMu terminal.domain terminal.left terminal.right := by
      rcases branch with branch | branch | branch <;> simp only [compileNode,branch]
    exact SourceCurrentNativeMuBodyOrigins.trace history terminal fuel result good (compiled ▸ actual) retained
  · intro entry body depth ordinary same
    exact SourceCurrentNativeOriginExposure.unfold_origin view valid entry body depth ordinary row (same ▸ origin)

/-- An actual request derives codecs and captured history from a complete origin at a separate view. -/
theorem request {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after)
    (view : Heap) (valid : InternedConstructorTemplates.Valid view)
    (row : EdgeValue Symbol Guard) (origin : Origin view [result] row) :
    History after ∧ Good after ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      ∃ terminal handle, Route after result input terminal ∧
        after.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
        (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
        (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
        Writer after handle terminal result ∧
        ∀ entry body depth ordinary, result = .mu entry body depth ordinary →
          Unfold view entry body depth ordinary row := by
  obtain ⟨first,second,key,left,right,keyed⟩ :=
    SourceCurrentNativeOriginExposure.keyable input fuel result actual view row origin
  obtain ⟨reached,checked,growth,observed⟩ :=
    SourceCurrentSharedLeafNativeLineage.request input fuel result good history actual
  have present : ∃ handle, after.native.nodes.cells handle = some ⟨input,.returned result⟩ := by
    rcases observed with ⟨missing,_⟩ | ⟨handle,cell,_⟩
    · rw [keyed] at missing
      cases missing
    · exact ⟨handle,cell⟩
  exact ⟨reached,checked,growth,returned reached input result ⟨first,left⟩ ⟨second,right⟩ present view valid row origin⟩

private theorem failed_body {before after : Checked width} (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

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

/-- An ordinary origin retains the exact paired child call and both strict source-child masses. -/
theorem ordinary {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (view : Heap) (row : EdgeValue Symbol Guard) (origin : Origin view [result] row)
    (childIndex : Nat) (value : Value Symbol Guard) (chosen : row.children[childIndex]? = some value) :
    ∃ (rowIndex leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (edgeHandle : Nat)
        (leftChild rightChild : Value Symbol Guard) (before after : Checked width) (fuel : Nat),
      (nodeEdges result)[rowIndex]? = some row ∧
      (nodeEdges request.left)[leftIndex]? = some leftRow ∧
      (nodeEdges request.right)[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      SourceCurrentNativeEdgeWriterGrowth.Written (width := width) edgeHandle ⟨request.domain,leftRow,rightRow⟩ row reader.native.machine.heap ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[childIndex]? = some leftChild ∧ rightRow.children[childIndex]? = some rightChild ∧
      InternedValueMass.value leftChild < InternedValueMass.value request.left ∧
      InternedValueMass.value rightChild < InternedValueMass.value request.right ∧
      Good before ∧ Good after ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧ Grows after.native.machine.heap reader.native.machine.heap ∧
      Trace fuel (.code (requestNode request.domain leftChild rightChild)) before (.code (.pure value)) after := by
  obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,_⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result present
  have payload := ordinary_payload request branch
  cases left : request.left <;> cases right : request.right <;>
    simp only [left,right,SourceRecursiveIntersectionControl.payload] at payload <;> try cases payload
  rename_i leftEntry leftRows leftDepth leftFree rightEntry rightRows rightDepth rightFree
  rw [←left,←right]
  have compiled : compileNode request = compileRows request.domain (nodeEdges request.left) (nodeEdges request.right) := by
    unfold compileNode
    simp only [branch]
    rw [left,right]
    rfl
  have body := compiled ▸ actual
  obtain ⟨index,selected⟩ := ordinary_origin (ordinary_result request.domain _ _ fuel result good body) view row origin
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,firstIndex,secondIndex,firstRow,secondRow,edge,
      firstChild,secondChild,current,next,count,firstFound,secondFound,symbols,written,symbol,guard,
      firstSelected,secondSelected,initial,final,firstGrowth,lastGrowth,called⟩ :=
    SourceCurrentNativeNodeRowLineage.ordinary history handle request result present
      leftEntry rightEntry leftRows rightRows leftDepth rightDepth leftFree rightFree left right branch
      index row selected childIndex value chosen
  have firstMass : InternedValueMass.value firstChild < InternedValueMass.value request.left := by
    rw [left]
    exact InternedValueMass.node_child_lt leftEntry leftRows leftDepth leftFree firstRow
      (by simpa only [left,nodeEdges] using List.mem_of_getElem? firstFound) firstChild (List.mem_of_getElem? firstSelected)
  have secondMass : InternedValueMass.value secondChild < InternedValueMass.value request.right := by
    rw [right]
    exact InternedValueMass.node_child_lt rightEntry rightRows rightDepth rightFree secondRow
      (by simpa only [right,nodeEdges] using List.mem_of_getElem? secondFound) secondChild (List.mem_of_getElem? secondSelected)
  exact ⟨index,firstIndex,secondIndex,firstRow,secondRow,edge,firstChild,secondChild,current,next,count,
    selected,firstFound,secondFound,symbols,written,symbol,guard,firstSelected,secondSelected,
    firstMass,secondMass,initial,final,firstGrowth,lastGrowth,called⟩

private theorem union_call {reader before after : Checked width} (history : History reader)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (side : Bool)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code ((SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members).bind
      (fun values => .work (makeUnion values) .pure))) before (.code (.pure result)) after)
    (retained : Retained after.native reader.native)
    (view : Heap) (row : EdgeValue Symbol Guard) (origin : Origin view [result] row) :
    ∃ values middle count,
      Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
        members before values middle count ∧
      ∃ index member value current next prefixFuel childFuel suffixFuel,
        members[index]? = some member ∧ values[index]? = some value ∧
        prefixFuel + childFuel + suffixFuel = count ∧
        Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
          (members.take index) before (values.take index) current prefixFuel ∧
        Good current ∧ Good next ∧
        Trace childFuel (.code (if side then requestNode domain member other else requestNode domain other member))
          current (.code (.pure value)) next ∧
        Retained next.native reader.native ∧
        Forwarded reader (if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩) current next value ∧
        Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
          (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel ∧ Origin view [value] row := by
  obtain ⟨values,middle,count,walked,indexed⟩ := SourceCurrentNativeOpenRowOrigins.union
    domain members other side fuel before after result good actual
  obtain ⟨inner,outer,rawValues,rawMiddle,_,first,made⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members))
    (fun values => .work (makeUnion values) .pure) before after result actual
  have same : rawValues = values ∧ rawMiddle = middle := by
    have firstDone := done_stable (inner + 1) (count + 1) _ before rawMiddle rawValues
      (trace_done inner _ before rawMiddle rawValues first.steps)
    have secondDone := done_stable (count + 1) (inner + 1) _ before middle values
      (trace_done count _ before middle values walked.trace.steps)
    rw [Nat.add_comm (count + 1) (inner + 1)] at secondDone
    exact Outcome.done.inj (firstDone.symm.trans secondDone)
  rcases same with ⟨sameValues,sameMiddle⟩
  subst rawValues
  subst rawMiddle
  have walkFields := SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations
    (fun member => if side then requestNode domain member other else requestNode domain other member)
    members (by intro member included; cases side <;> intro value <;> trivial)
  have middleFacts := effects walked.trace good walkFields
  obtain ⟨index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,total,prefixTrace,called,suffix,childOrigin⟩ := indexed view row origin
  have prefixFields := SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations
    (fun member => if side then requestNode domain member other else requestNode domain other member)
    (members.take index) (by intro member included; cases side <;> intro value <;> trivial)
  have currentFacts := effects prefixTrace.trace good prefixFields
  have actualChild : Trace childFuel (.code (requestNode
      ((if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩) : NodeRequest Symbol Guard).domain
      ((if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩) : NodeRequest Symbol Guard).left
      ((if side then ⟨domain,member,other⟩ else ⟨domain,other,member⟩) : NodeRequest Symbol Guard).right))
      current (.code (.pure value)) next := by cases side <;> exact called
  have nextFacts := effects actualChild currentFacts.1 (by intro value; trivial)
  have suffixRetained := SourceCurrentNativeWriterReadyRetention.trace_retained suffix.trace nextFacts.1.native.shape
  have finalRetained := SourceCurrentNativeWriterReadyRetention.trace_retained made middleFacts.1.native.shape
  have childRetained := suffixRetained.trans (finalRetained.trans retained)
  have forwarded := SourceCurrentNativeReferenceOrigins.forwarded history _ childFuel value currentFacts.1 actualChild childRetained
  exact ⟨values,middle,count,walked,index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,total,prefixTrace,currentFacts.1,nextFacts.1,called,childRetained,forwarded,suffix,childOrigin⟩

/-- A union origin at the given view selects one actual smaller source member and its captured child call. -/
theorem union {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (side : Bool)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right =
      if side then .leftUnion else .rightUnion)
    (view : Heap) (row : EdgeValue Symbol Guard) (origin : Origin view [result] row) :
    ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
        (depth : Nat) (free : List InternedBinderProtocol.Reference),
      (if side then request.left else request.right) = .union entry members depth free ∧
      ∃ (before after : Checked width) (fuel : Nat),
        Good before ∧ Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
        Grows before.native.machine.heap reader.native.machine.heap ∧ Grows after.native.machine.heap reader.native.machine.heap ∧
        Retained after.native reader.native ∧
        ∃ values middle count,
          Walk (fun member => if side then requestNode request.domain member request.right
            else requestNode request.domain request.left member) members before values middle count ∧
          ∃ index member value current next prefixFuel childFuel suffixFuel,
            members[index]? = some member ∧ values[index]? = some value ∧
            InternedValueMass.value member < InternedValueMass.value (if side then request.left else request.right) ∧
            prefixFuel + childFuel + suffixFuel = count ∧
            Walk (fun member => if side then requestNode request.domain member request.right
              else requestNode request.domain request.left member) (members.take index) before (values.take index) current prefixFuel ∧
            Good current ∧ Good next ∧
            Trace childFuel (.code (if side then requestNode request.domain member request.right
              else requestNode request.domain request.left member)) current (.code (.pure value)) next ∧
            Retained next.native reader.native ∧
            Forwarded reader (if side then ⟨request.domain,member,request.right⟩ else ⟨request.domain,request.left,member⟩)
              current next value ∧
            Walk (fun member => if side then requestNode request.domain member request.right
              else requestNode request.domain request.left member) (members.drop (index+1)) next (values.drop (index+1)) middle suffixFuel ∧
            Origin view [value] row := by
  obtain ⟨before,after,fuel,good,_,_,body,_,_,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result present
  have shape : ∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference),
      (if side then request.left else request.right) = .union entry members depth free := by
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at branch ⊢
    · cases selected : request.right with
      | union entry members depth free => exact ⟨entry,members,depth,free,rfl⟩
      | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
    · cases selected : request.left with
      | union entry members depth free => exact ⟨entry,members,depth,free,rfl⟩
      | empty | reference | node | mu =>
        have impossible := body
        unfold compileNode at impossible
        dsimp only at impossible
        rw [branch,selected] at impossible
        exact (failed_body fuel _ result impossible).elim
  obtain ⟨entry,members,depth,free,shape⟩ := shape
  have compiled : compileNode request =
      (SourceRecursiveIntersectionCode.walk (fun member => if side then requestNode request.domain member request.right
        else requestNode request.domain request.left member) members).bind (fun values => .work (makeUnion values) .pure) := by
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at branch shape ⊢ <;>
      unfold compileNode <;> dsimp only <;> rw [branch,shape]
  obtain ⟨values,middle,count,walked,index,member,value,current,next,prefixFuel,childFuel,suffixFuel,
    memberFound,valueFound,total,prefixTrace,initial,final,child,childRetained,forwarded,suffix,childOrigin⟩ :=
    union_call history request.domain members (if side then request.right else request.left) side
      fuel result good (by cases side <;> exact compiled ▸ body) retained view row origin
  have small := InternedValueMass.union_member_lt entry members depth free member (List.mem_of_getElem? memberFound)
  rw [←shape] at small
  refine ⟨entry,members,depth,free,shape,before,after,fuel,good,body,first,last,retained,values,middle,count,
    ?_,index,member,value,current,next,prefixFuel,childFuel,suffixFuel,memberFound,valueFound,small,total,
    ?_,initial,final,?_,childRetained,?_,?_,childOrigin⟩ <;> cases side <;> assumption

/-- A reference origin retains the exact entered read and ordered child call at the captured checked reader. -/
theorem reference {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (side : Bool)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right =
      if side then .leftReference else .rightReference)
    (view : Heap) (row : EdgeValue Symbol Guard) (origin : Origin view [result] row) :
    ∃ (before after : Checked width) (fuel : Nat),
      Good before ∧ Good after ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧ Grows after.native.machine.heap reader.native.machine.heap ∧
      Retained after.native reader.native ∧
      ∃ (name : Nat) (bound : Value Symbol Guard) (childFuel : Nat),
        (if side then request.left else request.right) = .reference (.interned name) ∧
        fuel = childFuel + 1 ∧ name ∈ SourceRecursiveIntersectionDomain.names request.domain.key ∧
        SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
        Trace childFuel (.code (if side then requestNode request.domain bound request.right
          else requestNode request.domain request.left bound)) before (.code (.pure result)) after ∧
        Forwarded reader (if side then ⟨request.domain,bound,request.right⟩ else ⟨request.domain,request.left,bound⟩)
          before after result ∧ Origin view [result] row := by
  obtain ⟨before,after,fuel,good,_,_,body,_,_,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result present
  cases side
  · obtain ⟨name,bound,count,shape,total,member,found,actual⟩ :=
      SourceCurrentNativeReferenceOrigins.right request fuel result body branch
    have checked := effects actual good (by intro value; trivial)
    exact ⟨before,after,fuel,good,checked.1,body,first,last,retained,name,bound,count,shape,total,member,found,actual,
      SourceCurrentNativeReferenceOrigins.forwarded history _ count result good actual retained,origin⟩
  · obtain ⟨name,bound,count,shape,total,member,found,actual⟩ :=
      SourceCurrentNativeReferenceOrigins.left request fuel result body branch
    have checked := effects actual good (by intro value; trivial)
    exact ⟨before,after,fuel,good,checked.1,body,first,last,retained,name,bound,count,shape,total,member,found,actual,
      SourceCurrentNativeReferenceOrigins.forwarded history _ count result good actual retained,origin⟩

end MicroCFTA.SourceCurrentNativeOriginViewBranches
