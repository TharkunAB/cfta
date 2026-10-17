import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceCurrentAllocatedNativeRequestResults
import MicroCFTA.SourceEqualityNativeDemandAcceptedReadback
import MicroCFTA.MergedFreshOrdinaryUnionOrigins

/-!
# Indexed rows and child calls in actual native code

Each indexed request retains its literal input and output state. Ordinary
row normalization can remove or reorder rows. Union normalization retains
complete epsilon row origins. These results verify physical traces and do
not assume a law about future callback outputs.
-/
namespace MicroCFTA.SourceCurrentNativeRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk bind_inverse walk_readback)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "NativeValid" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "Ready" => SourceEqualityRequiredCache.Ready
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every output occurrence names its original request and exact complete call states. -/
theorem indexed {A B : Type} {call : A → Code Symbol Guard B} {inputs : List A}
    {before after : Checked width} {values : List B} {fuel : Nat}
    (walk : Walk call inputs before values after fuel) (index : Nat) (value : B)
    (selected : values[index]? = some value) :
    ∃ request current next prefixFuel childFuel suffixFuel,
      inputs[index]? = some request ∧ prefixFuel + childFuel + suffixFuel = fuel ∧
      Walk call (inputs.take index) before (values.take index) current prefixFuel ∧
      Trace childFuel (.code (call request)) current (.code (.pure value)) next ∧
      Walk call (inputs.drop (index + 1)) next (values.drop (index + 1)) after suffixFuel := by
  induction walk generalizing index with
  | nil state => simp only [List.getElem?_nil] at selected; cases selected
  | cons first rest before middle after result results firstFuel restFuel called tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst value
          exact ⟨first, before, middle, 0, firstFuel, restFuel, rfl, by omega, .nil _, called, tail⟩
      | succ index =>
          obtain ⟨request, current, next, prefixFuel, childFuel, suffixFuel, found, count, initialCalls, child, suffix⟩ :=
            ih index (by simpa only [List.getElem?_cons_succ] using selected)
          refine ⟨request, current, next, firstFuel + prefixFuel, childFuel, suffixFuel, found, by omega, ?_, child, ?_⟩
          · simpa only [List.take_succ_cons] using Walk.cons first _ before middle current result _ firstFuel prefixFuel called initialCalls
          · simpa only [List.drop_succ_cons, Nat.add_assoc] using suffix

private theorem retains {A : Type} {fuel : Nat} {control : Control A} {before after : Checked width} {value : A}
    (trace : Trace fuel control before (.code (.pure value)) after)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap) :
    NativeValid after.native ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap := by
  have done := trace_done fuel control before after value trace.steps
  simpa only [done, Outcome.state] using SourceCurrentAllocatedNativePhysicalExecution.execute_invariants
    (fuel + 1) control before valid ready trace.plan

private theorem walk_nodes {A : Type} {requests : List A}
    (request : A → NodeRequest Symbol Guard) {before after : Checked width} {values : List (Value Symbol Guard)} {fuel : Nat}
    (walk : Walk (fun input => requestNode (request input).domain (request input).left (request input).right)
      requests before values after fuel)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap)
    (original : ∀ input ∈ requests, SourceRecursiveIntersectionInputView.Original (request input).left ∧
      SourceRecursiveIntersectionInputView.Original (request input).right) : Values after.native.machine.heap values := by
  induction walk with
  | nil => intro value member; cases member
  | cons input inputs before middle after value values firstFuel restFuel called tail ih =>
      have current := retains called valid ready
      have output := SourceCurrentAllocatedNativeRequestResults.node_result firstFuel (request input) before middle value
        valid (original input List.mem_cons_self).1 (original input List.mem_cons_self).2 called
      have later := ih current.1 current.2.2.ready (fun input member => original input (List.mem_cons_of_mem _ member))
      have growth := retains tail.trace current.1 current.2.2.ready
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact growth.2.2.available _ output
      · exact later child member

private theorem walk_edges {A : Type} {requests : List A}
    (request : A → EdgeRequest Symbol Guard) {before after : Checked width} {values : List (EdgeValue Symbol Guard)} {fuel : Nat}
    (walk : Walk (fun input => requestEdge (request input).domain (request input).left (request input).right)
      requests before values after fuel)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap) : Edges after.native.machine.heap values := by
  induction walk with
  | nil => intro value member; cases member
  | cons input inputs before middle after value values firstFuel restFuel called tail ih =>
      have current := retains called valid ready
      have output := SourceCurrentAllocatedNativeRequestResults.edge_result firstFuel (request input) before middle value valid called
      have later := ih current.1 current.2.2.ready
      have growth := retains tail.trace current.1 current.2.2.ready
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact edge_grows _ _ growth.2.2.growth _ output
      · exact later child member

/-- Accepted emitted children retain literal guard fields and an indexed ordered call history. -/
theorem children (request : EdgeRequest Symbol Guard) (combined : Allocated) (fuel : Nat)
    (before after : Checked width) (result : EdgeValue Symbol Guard)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap)
    (original : ∀ pair ∈ request.left.children.zip request.right.children,
      SourceRecursiveIntersectionInputView.Original pair.1 ∧ SourceRecursiveIntersectionInputView.Original pair.2)
    (trace : Trace fuel (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
      before (.code (.pure result)) after) :
    ∃ values middle count,
      Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children) before values middle count ∧
      result.entry.key.symbol = request.left.entry.key.symbol ∧
      result.entry.key.constraint = SourceEqualityConjoinAllocation.readback combined ∧ result.children = values ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap).2}} := by
  obtain ⟨inner, outer, values, middle, count, first, last⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun pair : Value Symbol Guard × Value Symbol Guard =>
      requestNode request.domain pair.1 pair.2) (request.left.children.zip request.right.children)))
    (fun values => .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure)
    before after result trace
  have current := retains first valid ready
  have walked := walk_readback _ _ inner _ _ _ first
  have available : Values middle.native.machine.heap values := walk_nodes (fun pair => ⟨request.domain,pair.1,pair.2⟩) walked valid ready original
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.native.machine.heap
    current.2.2.ready.semantic.1.normal.facts request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values available
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  exact ⟨values, middle, inner, walk_readback _ _ inner _ _ _ first,
    by simpa only [observed.1] using fields.1,
    by simpa only [observed.1] using fields.2.1,
    by simpa only [observed.1] using fields.2.2, observed.2⟩

/-- Canonical ordinary output rows retain indexed paired source rows and their literal edge calls. -/
theorem rows (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (before after : Checked width)
    (result : Value Symbol Guard) (valid : NativeValid before.native) (ready : Ready before.native.machine.heap)
    (trace : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after) :
    ∃ values middle count,
      Walk (fun pair => requestEdge domain pair.1 pair.2) (pairs left right) before values middle count ∧
      nodeEdges result = canonicalEdges (surviving values) ∧
      ∀ (outputIndex : Nat) (output : EdgeValue Symbol Guard), (nodeEdges result)[outputIndex]? = some output →
        ∃ scheduleIndex leftIndex rightIndex originalLeft originalRight current next prefixFuel childFuel suffixFuel,
          values[scheduleIndex]? = some output ∧
          (pairs left right)[scheduleIndex]? = some (originalLeft, originalRight) ∧
          left[leftIndex]? = some originalLeft ∧ right[rightIndex]? = some originalRight ∧
          originalLeft.entry.key.symbol = originalRight.entry.key.symbol ∧
          prefixFuel + childFuel + suffixFuel = count ∧
          Walk (fun pair => requestEdge domain pair.1 pair.2) ((pairs left right).take scheduleIndex)
            before (values.take scheduleIndex) current prefixFuel ∧
          Trace childFuel (.code (requestEdge domain originalLeft originalRight)) current (.code (.pure output)) next ∧
          Walk (fun pair => requestEdge domain pair.1 pair.2) ((pairs left right).drop (scheduleIndex + 1))
            next (values.drop (scheduleIndex + 1)) middle suffixFuel := by
  obtain ⟨inner, outer, values, middle, count, first, last⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard =>
      requestEdge domain pair.1 pair.2) (pairs left right))) (fun values => .work (makeNode values) .pure)
    before after result trace
  have current := retains first valid ready
  have walked := walk_readback _ _ inner _ _ _ first
  have resident : Edges middle.native.machine.heap values := walk_edges (fun pair => ⟨domain,pair.1,pair.2⟩) walked valid ready
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  have fields : nodeEdges result = canonicalEdges (surviving values) := by
    rw [observed.1]
    exact EqualityLeafProjectionPhysical.makeNode_edges values middle.native.machine.heap
      current.2.2.ready.semantic.1.normal.facts.coherent current.2.2.ready.semantic.1.normal.facts.linked resident
  refine ⟨values, middle, inner, walked, fields, ?_⟩
  intro outputIndex output selected
  have included : output ∈ canonicalEdges (surviving values) := by
    rw [fields] at selected
    exact List.mem_of_getElem? selected
  have member : output ∈ values := (List.mem_filter.mp (canonicalEdges_member _ output included)).1
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨pair, current, next, prefixFuel, childFuel, suffixFuel, input, counts, initialCalls, child, suffix⟩ := indexed walked index output found
  have originals := (pairs_member left right pair).mp (List.mem_of_getElem? input)
  obtain ⟨leftIndex, leftFound⟩ := List.mem_iff_getElem?.mp originals.1
  obtain ⟨rightIndex, rightFound⟩ := List.mem_iff_getElem?.mp originals.2.1
  exact ⟨index, leftIndex, rightIndex, pair.1, pair.2, current, next, prefixFuel, childFuel, suffixFuel,
    found, input, leftFound, rightFound, originals.2.2, counts, initialCalls, child, suffix⟩

/-- Union output epsilon rows retain indexed member results and their actual ordered call states. -/
theorem union (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (side : Bool) (fuel : Nat) (before after : Checked width) (result : Value Symbol Guard)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap)
    (original : ∀ member ∈ members, SourceRecursiveIntersectionInputView.Original member ∧
      SourceRecursiveIntersectionInputView.Original other)
    (trace : Trace fuel (.code ((SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members).bind
      (fun values => .work (makeUnion values) .pure))) before (.code (.pure result)) after) :
    ∃ values middle count,
      Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
        members before values middle count ∧
      ∀ (view : InternedConstructorTemplates.State Symbol Guard) (row : EdgeValue Symbol Guard),
        MergedFreshOrdinaryGraph.Origin view [result] row →
          ∃ index member value current next prefixFuel childFuel suffixFuel,
            members[index]? = some member ∧ values[index]? = some value ∧
            prefixFuel + childFuel + suffixFuel = count ∧
            Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
              (members.take index) before (values.take index) current prefixFuel ∧
            Trace childFuel (.code (if side then requestNode domain member other else requestNode domain other member))
              current (.code (.pure value)) next ∧
            Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
              (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel ∧
            MergedFreshOrdinaryGraph.Origin view [value] row := by
  obtain ⟨inner, outer, values, middle, count, first, last⟩ := bind_inverse fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members))
    (fun values => .work (makeUnion values) .pure) before after result trace
  have current := retains first valid ready
  have walked := walk_readback _ _ inner _ _ _ first
  have available : Values middle.native.machine.heap values := by
    let request := fun member => if side then (⟨domain,member,other⟩ : NodeRequest Symbol Guard) else ⟨domain,other,member⟩
    have same : (fun member => if side then requestNode domain member other else requestNode domain other member) =
      (fun member => requestNode (request member).domain (request member).left (request member).right) := by
      funext member; cases side <;> rfl
    rw [same] at walked
    apply walk_nodes request walked valid ready
    intro member included
    cases side with
    | false => exact (original member included).symm
    | true => exact original member included
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  refine ⟨values, middle, inner, walked, ?_⟩
  intro view row origin
  have included := (MergedFreshOrdinaryUnionOrigins.union_origins middle.native.machine.heap view
    current.2.2.ready.semantic.1.normal.facts current.2.2.ready.semantic.1.normal.live values available row).mp
    (by simpa only [observed.1] using origin)
  obtain ⟨value, member, origin⟩ := included
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨request, current, next, prefixFuel, childFuel, suffixFuel, input, counts, initialCalls, child, suffix⟩ := indexed walked index value found
  exact ⟨index, request, value, current, next, prefixFuel, childFuel, suffixFuel,
    input, found, counts, initialCalls, child, suffix, origin⟩

end MicroCFTA.SourceCurrentNativeRowOrigins
