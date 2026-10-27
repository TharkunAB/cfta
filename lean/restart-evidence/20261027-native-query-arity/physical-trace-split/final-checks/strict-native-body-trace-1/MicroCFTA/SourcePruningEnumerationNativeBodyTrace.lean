import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourcePruningEnumerationNativeBodyOriginArity

/-!
# Actual rich child traces of checked native edge bodies

The existing physical bind inverse retains every reached input check.
These consumers retain that rich trace and derive the current middle state.
The edge-body observer derives its actual accepted or sentinel branch.
No range predicate or future child result is supplied.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeBodyTrace
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WorkInputs" => SourceEqualityNativeDemandHeapPrimitives.WorkInputs
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {A B C : Type} {width : Nat}

/-- A rich ordered walk has one output for each actual input. -/
theorem walk_length [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : A → Code Symbol Guard B} {inputs : List A} {before after : Checked width}
    {values : List B} {fuel : Nat} (walk : Walk call inputs before values after fuel) :
    values.length = inputs.length := by
  induction walk with
  | nil => rfl
  | cons first rest before middle after value values firstFuel restFuel called tail ih =>
      exact congrArg Nat.succ ih

/-- Actual rich child prefixes retain their same middle invariants without a range forecast. -/
theorem cons_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (first : A) (rest : List A) (fuel : Nat)
    (before after : Checked width) (outputs : List B)
    (trace : Trace fuel (.code (SourceRecursiveIntersectionCode.walk call (first :: rest)))
      before (.code (.pure outputs)) after)
    (valid : Good before)
    (fields : Fields (.code (SourceRecursiveIntersectionCode.walk call (first :: rest))) before) :
    ∃ (firstFuel restFuel : Nat) (value : B) (values : List B) (middle : Checked width),
      firstFuel + restFuel = fuel ∧ outputs = value :: values ∧
      Trace firstFuel (.code (call first)) before (.code (.pure value)) middle ∧
      Trace restFuel (.code (SourceRecursiveIntersectionCode.walk call rest)) middle (.code (.pure values)) after ∧
      Good middle ∧ Extension before.native.machine middle.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations middle.operations ∧
      Fields (.code (call first)) before ∧
      Fields (.code (SourceRecursiveIntersectionCode.walk call rest)) middle ∧
      firstFuel ≤ fuel ∧ restFuel ≤ fuel := by
  let next := fun value => (SourceRecursiveIntersectionCode.walk call rest).bind
    fun values => .pure (value :: values)
  obtain ⟨firstFuel, tailFuel, value, middle, count, called, tailTrace⟩ :=
    SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse fuel (.code (call first))
      next before after outputs trace
  have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects (called.bind next) valid fields
  obtain ⟨restFuel, finalFuel, values, current, restCount, restTrace, finalTrace⟩ :=
    SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse tailFuel
      (.code (SourceRecursiveIntersectionCode.walk call rest))
      (fun values => .pure (value :: values)) middle after outputs tailTrace
  obtain ⟨rfl, rfl, rfl⟩ := pure_trace finalFuel (value :: values) outputs current after finalTrace.steps
  exact ⟨firstFuel, restFuel, value, values, middle, by omega, rfl, called, restTrace,
    reached.1, reached.2.1, reached.2.2.1, reached.2.2.2.1,
    SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
      (.code (call first)) next before fields,
    SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
      (.code (SourceRecursiveIntersectionCode.walk call rest)) (fun values => .pure (value :: values))
      middle reached.2.2.2.2, by omega, by omega⟩

/-- A rich child walk and its real final work retain exact fuel and every reached physical check. -/
theorem walk_work_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (inputs : List A) (finish : List B → Work Symbol Guard C)
    (fuel : Nat) (before after : Checked width) (value : C)
    (trace : Trace fuel
      (.code ((SourceRecursiveIntersectionCode.walk call inputs).bind fun values => .work (finish values) .pure))
      before (.code (.pure value)) after)
    (valid : Good before)
    (fields : Fields
      (.code ((SourceRecursiveIntersectionCode.walk call inputs).bind fun values => .work (finish values) .pure)) before) :
    ∃ (walkFuel : Nat) (values : List B) (middle : Checked width), fuel = walkFuel + 1 ∧
      Walk call inputs before values middle walkFuel ∧ Good middle ∧
      Extension before.native.machine middle.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations middle.operations ∧
      WorkInputs middle.native.machine.heap (finish values) ∧
      value = (run (finish values) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native
        {middle.native.machine with heap := (run (finish values) middle.native.machine.heap).2}} := by
  obtain ⟨inner, outer, values, middle, count, walked, finished⟩ :=
    SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse fuel
      (.code (SourceRecursiveIntersectionCode.walk call inputs))
      (fun values => .work (finish values) .pure) before after value trace
  have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects
    (walked.bind (fun values => .work (finish values) .pure)) valid fields
  obtain ⟨rfl, same, retained, operands⟩ :=
    SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback (finish values) outer middle after value finished
  exact ⟨inner, values, middle, count.symm,
    SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback call inputs inner before middle values walked,
    reached.1, reached.2.1, reached.2.2.1, reached.2.2.2.1, operands, same, retained⟩

private theorem body_first [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (value : EdgeValue Symbol Guard)
    (trace : Trace fuel (.edgeBody request .pure) before (.code (.pure value)) after) :
    ∃ code started rest,
      fuel = rest + 1 ∧
      SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) started ∧
      Trace rest (.code code) started (.code (.pure value)) after := by
  cases trace with
  | cons start state next current final reached count _inputs one tail =>
      obtain ⟨code, same⟩ := SourceEqualityNativeDemandBodyYield.pure_yielded_code
        request before current next one
      subst next
      exact ⟨code, current, count, rfl, one, tail⟩

/-- Every actual rich completed body derives its checked branch and rich ordered child origins. -/
theorem body_observation_rich [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (value : EdgeValue Symbol Guard)
    (trace : Trace fuel (.edgeBody request .pure) before (.code (.pure value)) after)
    (valid : Good before) (inputs : EdgeReady before.native.machine request) :
    ∃ code started rest,
      fuel = rest + 1 ∧
      SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) started ∧
      started.native = before.native ∧ Good started ∧ Fields (.code code) started ∧
      Trace rest (.code code) started (.code (.pure value)) after ∧ Good after ∧
      ((code = SourceEqualityNativeCheckedCode.sentinel request.left ∧ rest = 1 ∧
          WorkInputs started.native.machine.heap (makeEdge request.left.entry.key.symbol top [.empty]) ∧
          value = (run (makeEdge request.left.entry.key.symbol top [.empty]) started.native.machine.heap).1 ∧
          after = {started with native := advance started.native {started.native.machine with heap :=
            (run (makeEdge request.left.entry.key.symbol top [.empty]) started.native.machine.heap).2}}) ∨
        ∃ (first second combined : Allocated) (values : List (Value Symbol Guard))
          (middle : Checked width) (childFuel : Nat),
          SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first) ∧
          SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second) ∧
          (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
            request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
          code = SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined ∧
          started = {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le
            first second request.left.children.length request.right.children.length before.operations).2} ∧
          fuel = childFuel + 2 ∧
          Walk (fun pair => requestNode request.domain pair.1 pair.2)
            (request.left.children.zip request.right.children) started values middle childFuel ∧
          Good middle ∧ WorkInputs middle.native.machine.heap
            (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) ∧
          value = (run (makeEdge request.left.entry.key.symbol
            (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap).1 ∧
          after = {middle with native := advance middle.native {middle.native.machine with heap :=
            (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
              middle.native.machine.heap).2}} ∧ values.length = request.left.children.length) := by
  obtain ⟨code, started, rest, total, one, tail⟩ := body_first request fuel before after value trace
  have firstTrace : Trace 1 (.edgeBody request .pure) before (.code code) started :=
    .cons _ _ _ _ _ _ 0 (by trivial) one (.refl _ _)
  have startedEffects := SourceCurrentAllocatedNativeSemanticTraceReadback.effects firstTrace valid
    (show Fields (.edgeBody request .pure) before from ⟨inputs, fun _ => trivial⟩)
  have finalEffects := SourceCurrentAllocatedNativeSemanticTraceReadback.effects tail
    startedEffects.1 startedEffects.2.2.2.2
  obtain ⟨nativeSame, branch⟩ :=
    SourcePruningEnumerationNativeCheckedOriginArity.body_choice_checked request before started code one
  refine ⟨code, started, rest, total, one, nativeSame, startedEffects.1,
    startedEffects.2.2.2.2, tail, finalEffects.1, ?_⟩
  rcases branch with sentinelSame | ⟨first, second, combined, left, right, accepted, codeSame⟩
  · have actual : Trace rest (.code (.work (makeEdge request.left.entry.key.symbol top [.empty]) .pure))
        started (.code (.pure value)) after := by
      simpa only [sentinelSame, SourceEqualityNativeCheckedCode.sentinel] using tail
    obtain ⟨size, same, retained, operands⟩ :=
      SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback
        (makeEdge request.left.entry.key.symbol top [.empty]) rest started after value actual
    exact .inl ⟨sentinelSame, size, operands, same, retained⟩
  · have actual : Trace rest
        (.code ((SourceRecursiveIntersectionCode.walk (fun pair => requestNode request.domain pair.1 pair.2)
          (request.left.children.zip request.right.children)).bind fun values =>
            .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure))
        started (.code (.pure value)) after := by
      simpa only [codeSame, SourceEqualityNativeCheckedCode.children] using tail
    have actualFields : Fields
        (.code ((SourceRecursiveIntersectionCode.walk (fun pair => requestNode request.domain pair.1 pair.2)
          (request.left.children.zip request.right.children)).bind fun values =>
            .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure)) started := by
      simpa only [codeSame, SourceEqualityNativeCheckedCode.children] using startedEffects.2.2.2.2
    obtain ⟨childFuel, values, middle, counted, walked, good, _extension, _keeps, _operations,
        operands, same, retained⟩ := walk_work_readback
      (fun pair => requestNode request.domain pair.1 pair.2)
      (request.left.children.zip request.right.children)
      (fun values => makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
      rest started after value actual startedEffects.1 actualFields
    have arity : request.left.children.length = request.right.children.length := by
      by_cases equal : request.left.children.length = request.right.children.length
      · exact equal
      · have impossible := congrArg Prod.fst
          (SourceEqualityIntersectionEdgeAllocation.run_mismatch GuardStructuralOrder.le first second
            request.left.children.length request.right.children.length before.operations equal)
        rw [accepted] at impossible
        cases impossible
    have ready := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
      before arity first second combined left right accepted
    simp only [code_bind_pure] at ready
    have startedSame := (Outcome.yielded.inj (one.symm.trans ready)).2
    have lengthSame : values.length = request.left.children.length := by
      rw [walk_length walked, List.length_zip, arity, Nat.min_self]
    exact .inr ⟨first, second, combined, values, middle, childFuel, left, right, accepted,
      codeSame, startedSame, by omega, walked, good, operands, same, retained, lengthSame⟩

end MicroCFTA.SourcePruningEnumerationNativeBodyTrace
