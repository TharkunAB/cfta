import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
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
open SourceEqualityNativeDemandWalkExecution (Walk)
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
      Steps childFuel (.code (call request)) current (.code (.pure value)) next ∧
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
          obtain ⟨request, current, next, prefixFuel, childFuel, suffixFuel, found, count, prefix, child, suffix⟩ :=
            ih index (by simpa only [List.getElem?_cons_succ] using selected)
          refine ⟨request, current, next, firstFuel + prefixFuel, childFuel, suffixFuel, found, by omega, ?_, child, ?_⟩
          · simpa only [List.take_succ_cons] using Walk.cons first _ before middle current result _ firstFuel prefixFuel called prefix
          · simpa only [List.drop_succ_cons, Nat.add_assoc] using suffix

private theorem inputs_unbind {A B : Type} (control : Control A) (next : A → Code Symbol Guard B)
    (state : Checked width) (inputs : Inputs (control.bind next) state) : Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> exact inputs

/-- Splitting appended code retains every actual physical check and the exact full middle state. -/
theorem split {A B : Type} (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (value : B)
    (trace : Trace fuel (control.bind next) before (.code (.pure value)) after) :
    ∃ inner outer result current, inner + outer = fuel ∧
      Trace inner control before (.code (.pure result)) current ∧
      Trace outer (.code (next result)) current (.code (.pure value)) after := by
  induction fuel generalizing control before with
  | zero =>
      have same := steps_zero _ _ _ _ trace.steps
      cases control with
      | edgeBody => cases same.1
      | code code =>
          cases code with
          | pure result => exact ⟨0, 0, result, before, rfl, .refl _ _, trace⟩
          | fail | work | enter | read | optionalBinder | node | edge | finishNode | finishEdge => cases same.1
  | succ fuel ih =>
      cases trace with
      | cons _ _ rest current _ _ _ inputs one tail =>
          have boundStep := step_bind control next before
          cases original : step control before with
          | done result initial =>
              obtain ⟨pure, retained⟩ := (step_done_iff control before initial result).mp original
              subst control; subst initial
              exact ⟨0, fuel + 1, result, before, by omega, .refl _ _, .cons _ _ _ _ _ _ _ inputs one tail⟩
          | yielded body middle =>
              rw [original, appendStep] at boundStep
              have same := Outcome.yielded.inj (boundStep.symm.trans one)
              cases same.1; cases same.2
              obtain ⟨inner, outer, result, final, count, first, last⟩ := ih body middle tail
              exact ⟨inner + 1, outer, result, final, by omega,
                .cons _ _ _ _ _ _ _ (inputs_unbind control next before inputs) original first, last⟩
          | failed | constraintError | blocked =>
              rw [original, appendStep] at boundStep
              cases boundStep.symm.trans one

private theorem retains {A : Type} {fuel : Nat} {control : Control A} {before after : Checked width} {value : A}
    (trace : Trace fuel control before (.code (.pure value)) after)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap) :
    NativeValid after.native ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap := by
  have done := trace_done fuel control before after value trace.steps
  simpa only [done, Outcome.state] using SourceCurrentAllocatedNativePhysicalExecution.execute_invariants
    (fuel + 1) control before valid ready trace.plan

private theorem constructor_inputs {A : Type} {fuel : Nat} {job : Work Symbol Guard A}
    {before after : Checked width} {value : A}
    (trace : Trace fuel (.code (.work job .pure)) before (.code (.pure value)) after) :
    SourceEqualityNativeDemandHeapPrimitives.WorkInputs before.native.machine.heap job := by
  cases trace with
  | cons _ _ _ _ _ _ _ inputs _ _ => exact inputs

/-- Accepted emitted children retain literal guard fields and an indexed ordered call history. -/
theorem children (request : EdgeRequest Symbol Guard) (combined : Allocated) (fuel : Nat)
    (before after : Checked width) (result : EdgeValue Symbol Guard)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap)
    (trace : Trace fuel (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
      before (.code (.pure result)) after) :
    ∃ values middle count,
      Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children) before values middle count ∧
      result.entry.key.symbol = request.left.entry.key.symbol ∧
      result.entry.key.constraint = SourceEqualityConjoinAllocation.readback combined ∧ result.children = values ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap).2}} := by
  obtain ⟨inner, outer, values, middle, count, first, last⟩ := split fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun pair : Value Symbol Guard × Value Symbol Guard =>
      requestNode request.domain pair.1 pair.2) (request.left.children.zip request.right.children)))
    (fun values => .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure)
    before after result trace
  have current := retains first valid ready
  have available : Values middle.native.machine.heap values := by
    have inputs := constructor_inputs last
    cases inputs with | edge _ _ _ available => exact available
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.native.machine.heap
    current.2.2.ready.semantic.1.normal.facts request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values available
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  exact ⟨values, middle, inner, SourceEqualityNativeDemandWalkExecution.trace_walk _ _ inner _ _ _ first.steps,
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
          Steps childFuel (.code (requestEdge domain originalLeft originalRight)) current (.code (.pure output)) next ∧
          Walk (fun pair => requestEdge domain pair.1 pair.2) ((pairs left right).drop (scheduleIndex + 1))
            next (values.drop (scheduleIndex + 1)) middle suffixFuel := by
  obtain ⟨inner, outer, values, middle, count, first, last⟩ := split fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard =>
      requestEdge domain pair.1 pair.2) (pairs left right))) (fun values => .work (makeNode values) .pure)
    before after result trace
  have current := retains first valid ready
  have resident : Edges middle.native.machine.heap values := by
    have inputs := constructor_inputs last
    cases inputs with | node _ resident => exact resident
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  have fields : nodeEdges result = canonicalEdges (surviving values) := by
    rw [observed.1]
    exact EqualityLeafProjectionPhysical.makeNode_edges values middle.native.machine.heap
      current.2.2.ready.semantic.1.normal.facts.coherent current.2.2.ready.semantic.1.normal.facts.linked resident
  have walked := SourceEqualityNativeDemandWalkExecution.trace_walk _ _ inner _ _ _ first.steps
  refine ⟨values, middle, inner, walked, fields, ?_⟩
  intro outputIndex output selected
  have included : output ∈ canonicalEdges (surviving values) := by
    rw [fields] at selected
    exact List.mem_of_getElem? selected
  have member : output ∈ values := (List.mem_filter.mp (canonicalEdges_member _ output included)).1
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨pair, current, next, prefixFuel, childFuel, suffixFuel, input, counts, prefix, child, suffix⟩ := indexed walked index output found
  have originals := (pairs_member left right pair).mp (List.mem_of_getElem? input)
  obtain ⟨leftIndex, leftFound⟩ := List.mem_iff_getElem?.mp originals.1
  obtain ⟨rightIndex, rightFound⟩ := List.mem_iff_getElem?.mp originals.2.1
  exact ⟨index, leftIndex, rightIndex, pair.1, pair.2, current, next, prefixFuel, childFuel, suffixFuel,
    found, input, leftFound, rightFound, originals.2.2, counts, prefix, child, suffix⟩

/-- Union output epsilon rows retain indexed member results and their actual ordered call states. -/
theorem union (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (side : Bool) (fuel : Nat) (before after : Checked width) (result : Value Symbol Guard)
    (valid : NativeValid before.native) (ready : Ready before.native.machine.heap)
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
            Steps childFuel (.code (if side then requestNode domain member other else requestNode domain other member))
              current (.code (.pure value)) next ∧
            Walk (fun member => if side then requestNode domain member other else requestNode domain other member)
              (members.drop (index + 1)) next (values.drop (index + 1)) middle suffixFuel ∧
            MergedFreshOrdinaryGraph.Origin view [value] row := by
  obtain ⟨inner, outer, values, middle, count, first, last⟩ := split fuel
    (.code (SourceRecursiveIntersectionCode.walk (fun member =>
      if side then requestNode domain member other else requestNode domain other member) members))
    (fun values => .work (makeUnion values) .pure) before after result trace
  have current := retains first valid ready
  have available : Values middle.native.machine.heap values := by
    have inputs := constructor_inputs last
    cases inputs with | union _ available => exact available
  have observed := SourceEqualityNativeDemandAcceptedReadback.work_observation _ (outer + 1) middle after result
    (trace_done outer _ middle after result last.steps)
  have walked := SourceEqualityNativeDemandWalkExecution.trace_walk _ _ inner _ _ _ first.steps
  refine ⟨values, middle, inner, walked, ?_⟩
  intro view row origin
  have included := (MergedFreshOrdinaryUnionOrigins.union_origins middle.native.machine.heap view
    current.2.2.ready.semantic.1.normal.facts current.2.2.ready.semantic.1.normal.live values available row).mp
    (by simpa only [observed.1] using origin)
  obtain ⟨value, member, origin⟩ := included
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨request, current, next, prefixFuel, childFuel, suffixFuel, input, counts, prefix, child, suffix⟩ := indexed walked index value found
  exact ⟨index, request, value, current, next, prefixFuel, childFuel, suffixFuel,
    input, found, counts, prefix, child, suffix, origin⟩

end MicroCFTA.SourceCurrentNativeRowOrigins
