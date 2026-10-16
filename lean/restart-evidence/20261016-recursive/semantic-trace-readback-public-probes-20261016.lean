import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
open SourceCurrentAllocatedNativeSemanticTraceReadback
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.inputs_before_bind
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.code_fields_before_bind
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.after_step
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.effects
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.bind_readback
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.Walk.trace
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.cons_readback
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.walk_work_readback
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.inputs_before_bind
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.code_fields_before_bind
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.after_step
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.effects
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.bind_readback
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.Walk.trace
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.cons_readback
#check @MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback.walk_work_readback

namespace PhysicalReadbackChecks
noncomputable section
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

-- 1. A zero-length pure bind determines its actual child result and full state.
example (state : SourceEqualityNativeDemand.State 8) :
    ∃ inner outer result middle, inner + outer = 0 ∧
      Trace inner (.code (.pure (7 : Nat))) state (.code (.pure result)) middle ∧
      Trace outer (.code (.pure (result + 1))) middle (.code (.pure 8)) state :=
  bind_inverse 0 (.code (.pure 7)) (fun result => .pure (result + 1)) state state 8 (.refl _ _)

-- 2. A physical actual read splits before its distinct result continuation.
example (state : SourceEqualityNativeDemand.State 8) (name : Nat) :
    ∃ inner outer result middle, inner + outer = 1 ∧
      Trace inner (.code (.read name .pure)) state (.code (.pure result)) middle ∧
      Trace outer (.code (.pure result.isSome)) middle
        (.code (.pure (SourcePreparedSharedRows.read state.native.machine.heap name).isSome)) state := by
  apply bind_inverse 1 (.code (.read name .pure)) (fun result => .pure result.isSome) state state
    (SourcePreparedSharedRows.read state.native.machine.heap name).isSome
  exact .cons _ _ _ _ _ _ 0 trivial rfl (.refl _ _)

-- 3. Terminal pure work retains its literal result and complete reached state.
example (state : SourceEqualityNativeDemand.State 8) (value : Nat) :
    (value : Nat) = (InternedConstructorTemplates.run (.pure value) state.native.machine.heap).1 := by
  have trace : Trace 1 (.code (.work (.pure value) .pure)) state (.code (.pure value)) state :=
    .cons _ _ _ _ _ _ 0 (.pure value) rfl (.refl _ _)
  exact (work_readback (.pure value) 1 state state value trace).2.1

-- 4. An empty actual prefix derives all physical effects from the initial state.
example (state : SourceEqualityNativeDemand.State 8) (valid : Good state) :
    Good state ∧ SourceEqualityRequiredCache.Keeps state.native.machine.heap state.native.machine.heap := by
  have checked := effects (Trace.refl (.code (.pure (0 : Nat))) state) valid trivial
  exact ⟨checked.1, checked.2.2.1⟩

-- 5. Empty walk readback supplies its own exact empty output list.
example (call : Nat → Code Symbol Guard Nat) (state : SourceEqualityNativeDemand.State 8) :
    Walk call [] state [] state 0 := walk_readback call [] 0 state state [] (.refl _ _)

-- 6. A singleton raw read walk composes the same actual physical trace.
example (state : SourceEqualityNativeDemand.State 8) (name : Nat) :
    Trace 1 (.code (SourceRecursiveIntersectionCode.walk (fun name => .read name .pure) [name])) state
      (.code (.pure [SourcePreparedSharedRows.read state.native.machine.heap name])) state := by
  have called : Trace 1 (.code (.read name .pure)) state
      (.code (.pure (SourcePreparedSharedRows.read state.native.machine.heap name))) state :=
    .cons _ _ _ _ _ _ 0 trivial rfl (.refl _ _)
  exact (Walk.cons name [] state state state _ [] 1 0 called (.nil state)).trace

-- 7. First-step readback derives the exact remaining trace without a future answer.
example (state : SourceEqualityNativeDemand.State 8) (name : Nat) :
    ∃ count, 1 = count + 1 ∧ Trace count
      (.code (.pure (SourcePreparedSharedRows.read state.native.machine.heap name))) state
      (.code (.pure (SourcePreparedSharedRows.read state.native.machine.heap name))) state := by
  apply after_step 1 (.code (.read name .pure)) _ state state state _
  · exact .cons _ _ _ _ _ _ 0 trivial rfl (.refl _ _)
  · rfl

-- 8. A read continuation's fields are checked in the original operation cache.
example (operations : SourceEqualityConstraintMemoAllocation.State) (name : Nat)
    (next : Option (Value Symbol Guard) → Code Symbol Guard Nat)
    (later : Nat → Code Symbol Guard Bool)
    (fields : SourceCurrentAllocatedNativeCodeFields.Fields operations ((Code.read name next).bind later)) :
    SourceCurrentAllocatedNativeCodeFields.Fields operations (.read name next) :=
  code_fields_before_bind operations (.read name next) later fields

-- 9. Optional-binder availability is an input check of the earlier actual instruction.
example (state : SourceEqualityNativeDemand.State 8) (key : Nat × Nat) (body : Value Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard Nat) (later : Nat → Code Symbol Guard Bool)
    (available : SourceCurrentAllocatedNativePhysicalExecution.Inputs
      ((Control.code (.optionalBinder key body next)).bind later) state) :
    Available state.native.machine.heap body :=
  inputs_before_bind (.code (.optionalBinder key body next)) later state available

-- 10. Nonempty walk readback derives its intermediate invariants and tail ranges.
example (call : Nat → Code Symbol Guard Nat) (first : Nat) (rest : List Nat) (fuel : Nat)
    (before after : SourceEqualityNativeDemand.State 8) (outputs : List Nat)
    (trace : Trace fuel (.code (SourceRecursiveIntersectionCode.walk call (first :: rest))) before (.code (.pure outputs)) after)
    (valid : Good before) (fields : Fields (.code (SourceRecursiveIntersectionCode.walk call (first :: rest))) before)
    (ranges : WordRanges (.code (SourceRecursiveIntersectionCode.walk call (first :: rest))) before) :
    ∃ (value : Nat) (values : List Nat) (middle : SourceEqualityNativeDemand.State 8), outputs = value :: values ∧ Good middle ∧
      WordRanges (.code (SourceRecursiveIntersectionCode.walk call rest)) middle := by
  obtain ⟨_, _, value, values, middle, _, shape, _, _, good, _, _, _, _, _, tailRanges⟩ :=
    cons_readback call first rest fuel before after outputs trace valid fields ranges
  exact ⟨value, values, middle, shape, good, tailRanges⟩
end
end PhysicalReadbackChecks
