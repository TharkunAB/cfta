import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

/-!
# Checked physical traces through protected completion frames

Each yielded instruction retains its actual physical input check.
Trace composition retains the whole checked state and operation cache.
Completion derives its physical plan from the constructed trace.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "ActiveAbove" => SourceRecursiveIntersectionNative.ActiveAbove
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

variable {A B : Type} {width fuel extra : Nat}
variable {control next middle rest : Control A} {state before current after : Checked width}
variable {value : A} {post : Machine Symbol Guard → A → Prop}

/-- Each actual yielded instruction records its current physical check. -/
inductive Trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control A → Checked width → Control A → Checked width → Prop where
  | refl (control : Control A) (state : Checked width) : Trace 0 control state control state
  | cons (control : Control A) (state : Checked width) (next : Control A) (after : Checked width)
      (final : Control A) (result : Checked width) (fuel : Nat)
      (inputs : Inputs control state)
      (actual : step control state = .yielded next after)
      (rest : Trace fuel next after final result) : Trace (fuel + 1) control state final result

/-- Erasure retains the literal yielded controls and all current state fields. -/
theorem Trace.steps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Trace fuel control state next after) : Steps fuel control state next after := by
  induction trace with
  | refl => exact .refl _ _
  | cons _ _ _ _ _ _ _ _ one _ ih => exact .cons _ _ _ _ _ _ _ one ih

/-- Actual physical traces compose at the same returned control and state. -/
theorem Trace.trans [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (first : Trace fuel control state middle current) (second : Trace extra middle current next after) :
    Trace (fuel + extra) control state next after := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | cons start before resume reached final result count inputs one rest ih =>
      simpa only [Nat.succ_add] using Trace.cons start before resume reached next after (count + extra) inputs one (ih second)

private theorem inputs_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control rest : Control A) (next : A → Code Symbol Guard B) (state after : Checked width)
    (inputs : Inputs control state) (one : step control state = .yielded rest after) :
    Inputs (control.bind next) state := by
  cases control with
  | edgeBody => trivial
  | code code =>
      cases code with
      | pure value => simp only [step, SourceRecursiveIntersectionNative.step, lift] at one; cases one
      | fail | work | enter | read | optionalBinder | node | edge | finishNode | finishEdge => exact inputs

/-- Appending a continuation retains all reached physical checks before its first instruction. -/
theorem Trace.bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Trace fuel control state rest after) (next : A → Code Symbol Guard B) :
    Trace fuel (control.bind next) state (rest.bind next) after := by
  induction trace with
  | refl => exact .refl _ _
  | cons control state middle current final result count inputs one tail ih =>
      apply Trace.cons _ _ _ _ _ _ _ (inputs_bind control middle next state current inputs one)
      · rw [step_bind, one]
        rfl
      · exact ih

/-- A constructed pure-return trace derives every physical check through its final return. -/
theorem Trace.plan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Trace fuel control state (.code (.pure value)) after) :
    SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (fuel + 1) control state := by
  induction fuel generalizing control state with
  | zero => cases trace; exact ⟨trivial, trivial⟩
  | succ fuel ih =>
      cases trace with
      | cons control state next current final result count inputs one rest =>
          exact ⟨inputs, by simpa only [one] using ih rest⟩

/-- Returned physical execution records its own trace, effects, and structural postcondition. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (before : Checked width) (value : A) (after : Checked width)
    (post : Machine Symbol Guard → A → Prop) : Prop where
  trace : Trace fuel control before (.code (.pure value)) after
  good : Good after
  extension : Extension before.native.machine after.native.machine
  keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap
  operations : SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations
  result : post after.native.machine value

/-- The actual returned value has a finite physical trace and its structural postcondition. -/
def Returned [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (before : Checked width) (post : Machine Symbol Guard → A → Prop) : Prop :=
  ∃ fuel value after, Receipt fuel control before value after post

/-- A physical return receipt completes the exact checked interpreter. -/
theorem Receipt.done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (receipt : Receipt fuel control before value after post) :
    SourceEqualityNativeDemand.execute (fuel + 1) control before = .done value after :=
  trace_done fuel control before after value receipt.trace.steps

private theorem operations_trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) :
    SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations, Cache.extends_trans first.descents second.descents⟩

private theorem before_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control A) (state current : Checked width) (post : Machine Symbol Guard → A → Prop)
    (valid : Good state) (inputs : Inputs control state) (fields : Fields control state)
    (one : step control state = .yielded next current) (later : Returned next current post) :
    Returned control state post := by
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control state valid inputs fields
  have currentEffects : Good current ∧ Extension state.native.machine current.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap current.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations current.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (.yielded next current) := by
    simpa only [one, Outcome.state] using checked
  obtain ⟨fuel, value, after, receipt⟩ := later
  exact ⟨fuel + 1, value, after, ⟨.cons _ _ _ _ _ _ _ inputs one receipt.trace, receipt.good,
    currentEffects.2.1.trans receipt.extension, currentEffects.2.2.1.trans receipt.keeps,
    operations_trans currentEffects.2.2.2.1 receipt.operations, receipt.result⟩⟩


private theorem yielded_good [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control A) (state current : Checked width) (valid : Good state)
    (inputs : Inputs control state) (fields : Fields control state)
    (one : step control state = .yielded next current) : Good current ∧ Fields next current := by
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control state valid inputs fields
  have effects : Good current ∧ Extension state.native.machine current.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap current.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations current.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (.yielded next current) := by
    simpa only [one, Outcome.state] using checked
  exact ⟨effects.1, effects.2.2.2.2.2⟩

private theorem join [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (state current : Checked width) (value : A) (fuel : Nat)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (body : Receipt fuel control state value current intermediate) (next : A → Code Symbol Guard B)
    (later : Returned (.code (next value)) current post) : Returned (control.bind next) state post := by
  obtain ⟨count, output, after, receipt⟩ := later
  exact ⟨fuel + count, output, after,
    ⟨(body.trace.bind next).trans receipt.trace, receipt.good, body.extension.trans receipt.extension,
      body.keeps.trans receipt.keeps, operations_trans body.operations receipt.operations, receipt.result⟩⟩

private structure Bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound width : Nat) : Prop where
  nodes : ∀ request : NodeRequest Symbol Guard, NodeScope source request →
    ∀ complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request),
    requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete < bound →
    ∀ state : Checked width, Good state → NodeReady state.native.machine request →
    Grows source state.native.machine.heap → Extends source.nodes.issued state.native.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete) state.native →
    WordRanges (.code (compileNode request)) state →
    Returned (.code (compileNode request)) state (fun after value => Available after.heap value)
  edges : ∀ request : EdgeRequest Symbol Guard, EdgeScope source request →
    ∀ complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request),
    requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete < bound →
    ∀ state : Checked width, Good state → EdgeReady state.native.machine request →
    Grows source state.native.machine.heap → Extends source.nodes.issued state.native.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete) state.native →
    WordRanges (.edgeBody request .pure) state →
    Returned (.edgeBody request .pure) state (fun after value => EdgeResident after.heap value)

private theorem node_of_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (bodies : Bodies source holds bound width) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (state : Checked width) (post : Machine Symbol Guard → A → Prop)
    (valid : Good state) (ready : NodeReady state.native.machine request) (below : NodeBelow source holds bound request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds bound state.native) (ranges : WordRanges (.code (.node request next)) state)
    (fields : ∀ value, CodeFields state.operations (next value))
    (later : ∀ (value : Value Symbol Guard) (after : Checked width), Good after → Extension state.native.machine after.native.machine →
      Available after.native.machine.heap value → ActiveAbove (view source holds) holds bound after.native →
      WordRanges (.code (next value)) after → CodeFields after.operations (next value) →
      Returned (.code (next value)) after post) : Returned (.code (.node request next)) state post := by
  obtain ⟨scope, complete, smaller⟩ := below
  let limit := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete
  have words := ranges.current (.code (.node request next)) state
  have inputs : Inputs (.code (.node request next)) state := ⟨ready, words⟩
  cases selected : lookupNode width request state.native with
  | mk selection chosen =>
    cases selection with
    | direct original =>
      obtain ⟨same, retained⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request original state.native chosen selected
      subst original
      subst chosen
      have one : step (.code (.node request next)) state = .yielded (.code ((compileNode request).bind next)) state := by
        simp only [step, SourceRecursiveIntersectionNative.step, selected, lift]
      have entered := ranges.after_step _ _ _ _ one
      have bodyRanges := entered.before_bind (.code (compileNode request)) next state
      obtain ⟨fuel, value, current, body⟩ := bodies.nodes request scope complete smaller state valid ready growth history
        (active.weaken _ holds bound limit (Nat.le_of_lt smaller) _) bodyRanges
      have afterActive := active.running_before _ holds bound state.native current.native
        (SourceCurrentAllocatedNativeRunning.trace_running_before fuel _ state current value body.trace.steps
          (compileNode_bodyCode request) valid.native.shape)
      have nextFields := SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations current.operations
        (next value) (fields value) body.operations
      have tail := later value current body.good body.extension body.result afterActive
        (entered.after_body (.code (compileNode request)) next state current fuel value body.trace.steps) nextFields
      exact before_step _ _ state state post valid inputs fields one (join _ state current value fuel _ post body next tail)
    | memoized handle =>
      obtain ⟨key, requested, _, chosenMachine⟩ := SourceRecursiveIntersectionNative.lookupNode_memoized request state.native chosen handle selected
      have safe := words key requested
      have chosenActive : ActiveAbove (view source holds) holds bound chosen := by
        simpa only [selected] using active.lookupNode _ holds bound state.native request
      cases demanded : demandNode handle chosen with
      | mk observation current =>
        cases observation with
        | absent => exact False.elim (SourceRecursiveIntersectionNative.node_absent_impossible state.native chosen current
            valid.native.shape request handle selected demanded)
        | busy => exact False.elim (SourceCurrentAllocatedNativePhysicalExecution.node_busy_impossible (view source holds) holds bound
            state.native chosen current valid.native active request ready safe complete smaller handle selected demanded)
        | ready value =>
          have returned := SourceCurrentAllocatedNativePhysicalCache.node_ready request state.native chosen current handle value
            valid.native ready safe selected demanded
          let after : Checked width := ⟨current, state.operations⟩
          have one : step (.code (.node request next)) state = .yielded (.code (next value)) after := by
            simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, after]
          have afterGood := yielded_good _ _ state after valid inputs fields one
          have sameMachine : current.machine = state.native.machine := by rw [returned.2.1]; exact chosenMachine
          have physical : Extension state.native.machine current.machine := by rw [sameMachine]; exact .refl _
          have afterActive : ActiveAbove (view source holds) holds bound current := by rw [returned.2.1]; exact chosenActive
          exact before_step _ _ state after post valid inputs fields one
            (later value after afterGood.1 physical returned.2.2 afterActive (ranges.after_step _ _ _ _ one) afterGood.2)
        | evaluate original =>
          have same := SourceCurrentAllocatedNativePhysicalCache.node_started request original state.native chosen current handle
            valid.native ready safe selected demanded
          subst original
          let start : Checked width := ⟨current, state.operations⟩
          let frame := fun value => Code.finishNode handle value (next value)
          have one : step (.code (.node request next)) state = .yielded (.code ((compileNode request).bind frame)) start := by
            simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, frame, start]
          have startGood := (yielded_good _ _ state start valid inputs fields one).1
          have sameMachine : current.machine = state.native.machine :=
            (show current.machine = chosen.machine from by
              simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_machine handle chosen).trans chosenMachine
          have startReady : NodeReady current.machine request := by rw [sameMachine]; exact ready
          have startActive := (chosenActive.weaken _ holds bound limit (Nat.le_of_lt smaller) _).startNode
            (view source holds) holds limit chosen current handle request demanded complete (Nat.le_refl _)
          have entered := ranges.after_step _ _ _ _ one
          have bodyRanges := entered.before_bind (.code (compileNode request)) frame start
          obtain ⟨fuel, value, middle, body⟩ := bodies.nodes request scope complete smaller start startGood startReady
            (by rw [sameMachine]; exact growth) (by rw [sameMachine]; exact history) startActive bodyRanges
          have running := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen current request demanded).2
          have preserved := SourceEqualityNativeDemandRunning.node_body_cell (fuel + 1) handle request start middle value
            startGood.native.shape running body.done
          let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishNode handle value middle.native}
          have finishInputs : Inputs (.code (frame value)) middle := ⟨request, preserved.1, body.result⟩
          have finishFields : Fields (.code (frame value)) middle :=
            SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations middle.operations (next value)
              (fields value) body.operations
          have finishStep : step (.code (frame value)) middle = .yielded (.code (next value)) finished := rfl
          have finishedGood := yielded_good _ _ middle finished body.good finishInputs finishFields finishStep
          have physical : Extension state.native.machine finished.native.machine := by
            change Extension state.native.machine middle.native.machine
            rw [← sameMachine]
            exact body.extension
          have afterActive := SourceCurrentAllocatedNativeRunning.node_finish_active (view source holds) holds bound
            fuel handle request chosen start middle value chosenActive demanded startGood.native.shape body.trace.steps
          have atFrame := entered.after_body (.code (compileNode request)) frame start middle fuel value body.trace.steps
          have tail := later value finished finishedGood.1 physical body.result afterActive
            (atFrame.after_step _ _ _ _ finishStep) finishedGood.2
          have framed := before_step _ _ middle finished post body.good finishInputs finishFields finishStep tail
          exact before_step _ _ state start post valid inputs fields one
            (join _ start middle value fuel _ post body frame framed)


private theorem edge_of_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (bodies : Bodies source holds bound width) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (state : Checked width) (post : Machine Symbol Guard → A → Prop)
    (valid : Good state) (ready : EdgeReady state.native.machine request) (below : EdgeBelow source holds bound request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds bound state.native) (ranges : WordRanges (.code (.edge request next)) state)
    (fields : ∀ value, CodeFields state.operations (next value))
    (later : ∀ (value : EdgeValue Symbol Guard) (after : Checked width), Good after → Extension state.native.machine after.native.machine →
      EdgeResident after.native.machine.heap value → ActiveAbove (view source holds) holds bound after.native →
      WordRanges (.code (next value)) after → CodeFields after.operations (next value) →
      Returned (.code (next value)) after post) : Returned (.code (.edge request next)) state post := by
  obtain ⟨scope, complete, smaller⟩ := below
  let limit := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete
  have words := ranges.current (.code (.edge request next)) state
  have inputs : Inputs (.code (.edge request next)) state := ⟨ready, words⟩
  cases selected : lookupEdge width request state.native with
  | mk handle chosen =>
    have chosenMachine : chosen.machine = state.native.machine := by
      simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request state.native
    have chosenActive : ActiveAbove (view source holds) holds bound chosen := by
      simpa only [selected] using active.lookupEdge _ holds bound state.native request
    cases demanded : demandEdge handle chosen with
    | mk observation current =>
      cases observation with
      | absent => exact False.elim (SourceRecursiveIntersectionNative.edge_absent_impossible state.native chosen current
          valid.native.shape request handle selected demanded)
      | busy => exact False.elim (SourceCurrentAllocatedNativePhysicalExecution.edge_busy_impossible (view source holds) holds bound
          state.native chosen current valid.native active request ready words complete smaller handle selected demanded)
      | ready value =>
        have returned := SourceCurrentAllocatedNativePhysicalCache.edge_ready request state.native chosen current handle value
          valid.native ready words selected demanded
        let after : Checked width := ⟨current, state.operations⟩
        have one : step (.code (.edge request next)) state = .yielded (.code (next value)) after := by
          simp only [step, selected, demanded, after]
        have afterGood := yielded_good _ _ state after valid inputs fields one
        have sameMachine : current.machine = state.native.machine := by rw [returned.2.1]; exact chosenMachine
        have physical : Extension state.native.machine current.machine := by rw [sameMachine]; exact .refl _
        have afterActive : ActiveAbove (view source holds) holds bound current := by rw [returned.2.1]; exact chosenActive
        exact before_step _ _ state after post valid inputs fields one
          (later value after afterGood.1 physical returned.2.2 afterActive (ranges.after_step _ _ _ _ one) afterGood.2)
      | evaluate original =>
        have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request original state.native chosen current handle
          valid.native ready words selected demanded
        subst original
        let start : Checked width := ⟨current, state.operations⟩
        let frame := fun value => Code.finishEdge handle value (next value)
        have one : step (.code (.edge request next)) state = .yielded (.edgeBody request frame) start := by
          simp only [step, selected, demanded, frame, start]
        have startGood := (yielded_good _ _ state start valid inputs fields one).1
        have sameMachine : current.machine = state.native.machine :=
          (show current.machine = chosen.machine from by
            simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen).trans chosenMachine
        have startReady : EdgeReady current.machine request := by rw [sameMachine]; exact ready
        have startActive := (chosenActive.weaken _ holds bound limit (Nat.le_of_lt smaller) _).startEdge
          (view source holds) holds limit chosen current handle request demanded complete (Nat.le_refl _)
        have entered := ranges.after_step _ _ _ _ one
        have bodyRanges := entered.before_bind (.edgeBody request .pure) frame start
        obtain ⟨fuel, value, middle, body⟩ := bodies.edges request scope complete smaller start startGood startReady
          (by rw [sameMachine]; exact growth) (by rw [sameMachine]; exact history) startActive bodyRanges
        have running := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen current request demanded).2
        have preserved := SourceEqualityNativeDemandRunning.edge_body_cell (fuel + 1) handle request start middle value
          startGood.native.shape running body.done
        let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle value middle.native}
        have finishInputs : Inputs (.code (frame value)) middle := ⟨request, preserved.1, body.result⟩
        have finishFields : Fields (.code (frame value)) middle :=
          SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations middle.operations (next value)
            (fields value) body.operations
        have finishStep : step (.code (frame value)) middle = .yielded (.code (next value)) finished := rfl
        have finishedGood := yielded_good _ _ middle finished body.good finishInputs finishFields finishStep
        have physical : Extension state.native.machine finished.native.machine := by
          change Extension state.native.machine middle.native.machine
          rw [← sameMachine]
          exact body.extension
        have afterActive := SourceCurrentAllocatedNativeRunning.edge_finish_active (view source holds) holds bound
          fuel handle request chosen start middle value chosenActive demanded startGood.native.shape body.trace.steps
        have atFrame := entered.after_body (.edgeBody request .pure) frame start middle fuel value body.trace.steps
        have tail := later value finished finishedGood.1 physical body.result afterActive
          (atFrame.after_step _ _ _ _ finishStep) finishedGood.2
        have framed := before_step _ _ middle finished post body.good finishInputs finishFields finishStep tail
        exact before_step _ _ state start post valid inputs fields one
          (join _ start middle value fuel _ post body frame framed)


private theorem code_of_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (bodies : Bodies source holds bound width) (code : Code Symbol Guard A) :
    ∀ (state : Checked width) (post : Machine Symbol Guard → A → Prop),
    Safe code state.native.machine post → SourceCurrentAllocatedNativeCodeProgress.Operands code state.native.machine →
    Below source holds bound code state.native.machine → Good state → CodeFields state.operations code →
    Grows source state.native.machine.heap → Extends source.nodes.issued state.native.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds bound state.native → WordRanges (.code code) state →
    Returned (.code code) state post := by
  induction code with
  | pure value =>
      intro state post safe _ _ valid _ _ _ _ _
      exact ⟨0, value, state, ⟨.refl _ _, valid, .refl _, SourceEqualityRequiredCache.pure_keeps _ valid.heap,
        SourceEqualityConstraintMemoAllocation.grows_refl _, safe⟩⟩
  | fail failure => intro _ _ _ _ impossible; cases impossible
  | work job next ih =>
      intro state post safe operands below valid fields growth history active ranges
      let actual := InternedConstructorTemplates.run job state.native.machine.heap
      let machine : Machine Symbol Guard := {state.native.machine with heap := actual.2}
      let after : Checked width := {state with native := advance state.native machine}
      have one : step (.code (.work job next)) state = .yielded (.code (next actual.1)) after := rfl
      have checked := yielded_good (.code (.work job next)) (.code (next actual.1)) state after valid operands.1 fields one
      have call : SourceRecursiveIntersectionKernel.work job state.native.machine = .done actual.1 machine := rfl
      have physical : Extension state.native.machine machine := safe.2.1
      exact before_step (.code (.work job next)) (.code (next actual.1)) state after post valid operands.1 fields one
        (ih actual.1 after post (safe.2.2 _ _ call) (operands.2 _ _ call) (below _ _ call)
          checked.1 checked.2 (grows_trans growth physical.heap) (extends_trans history physical.history)
          (active.advance _ holds bound _ machine) (ranges.after_step _ _ _ _ one))
  | enter domain left right first second next ih =>
      intro state post safe operands below valid fields growth history active ranges
      let actual := SourceRecursiveIntersectionEnvironment.enter state.native.machine.domains domain.key left right first second
      let machine : Machine Symbol Guard := {state.native.machine with domains := actual.2}
      let after : Checked width := {state with native := advance state.native machine}
      have inputs : Inputs (.code (.enter domain left right first second next)) state :=
        ⟨operands.1, operands.2.1, operands.2.2.1⟩
      have one : step (.code (.enter domain left right first second next)) state = .yielded (.code (next actual.1)) after := rfl
      have checked := yielded_good _ _ state after valid inputs fields one
      have physical : Extension state.native.machine machine := safe.2.1
      exact before_step _ _ state after post valid inputs fields one
        (ih actual.1 after post safe.2.2 operands.2.2.2 below checked.1 checked.2
          (grows_trans growth physical.heap) (extends_trans history physical.history)
          (active.advance _ holds bound _ machine) (ranges.after_step _ _ _ _ one))
  | read name next ih =>
      intro state post safe operands below valid fields growth history active ranges
      have one : step (.code (.read name next)) state =
          .yielded (.code (next (SourcePreparedSharedRows.read state.native.machine.heap name))) state := rfl
      exact before_step _ _ state state post valid trivial fields one
        (ih _ state post safe operands below valid (fields _) growth history active (ranges.after_step _ _ _ _ one))
  | optionalBinder key body next ih =>
      intro state post safe operands below valid fields growth history active ranges
      obtain ⟨value, heap, done, _, _⟩ := SourceEqualityNativeDemandHeapPrimitives.optionalBinder_complete
        key body state.native.machine.heap valid.heap operands.1
      let machine : Machine Symbol Guard := {state.native.machine with heap := heap}
      let after : Checked width := {state with native := advance state.native machine}
      have call : construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.native.machine.heap)
          state.native.machine = .done value machine := by simp only [done, construction]; rfl
      have one : step (.code (.optionalBinder key body next)) state = .yielded (.code (next value)) after := by
        simp only [step, SourceRecursiveIntersectionNative.step, done, lift, after, machine]
      have checked := yielded_good (.code (.optionalBinder key body next)) (.code (next value)) state after valid operands.1 fields one
      have physical : Extension state.native.machine machine := by simpa only [call, Result.state] using safe.2.1
      exact before_step (.code (.optionalBinder key body next)) (.code (next value)) state after post valid operands.1 fields one
        (ih value after post (safe.2.2 _ _ call) (operands.2 _ _ call) (below _ _ call)
          checked.1 checked.2 (grows_trans growth physical.heap) (extends_trans history physical.history)
          (active.advance _ holds bound _ machine) (ranges.after_step _ _ _ _ one))
  | node request next ih =>
      intro state post safe operands below valid fields growth history active ranges
      apply node_of_bodies source holds bound bodies request next state post valid safe.1 below.1 growth history active ranges fields
      intro value after afterGood physical available afterActive afterRanges afterFields
      exact ih value after post (safe.2 _ _ afterGood.native.machine physical available)
        (operands.2 _ _ afterGood.native.machine physical available) (below.2 _ _ afterGood.native.machine physical available)
        afterGood afterFields (grows_trans growth physical.heap) (extends_trans history physical.history) afterActive afterRanges
  | edge request next ih =>
      intro state post safe operands below valid fields growth history active ranges
      apply edge_of_bodies source holds bound bodies request next state post valid safe.1 below.1 growth history active ranges fields
      intro value after afterGood physical available afterActive afterRanges afterFields
      exact ih value after post (safe.2 _ _ afterGood.native.machine physical available)
        (operands.2 _ _ afterGood.native.machine physical available) (below.2 _ _ afterGood.native.machine physical available)
        afterGood afterFields (grows_trans growth physical.heap) (extends_trans history physical.history) afterActive afterRanges
  | finishNode | finishEdge => intro _ _ _ _ impossible; cases impossible


private theorem all_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) : Bodies source holds bound width := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      constructor
      · intro request scope complete smaller state valid ready growth history active ranges
        let limit := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete
        have bodies : Bodies source holds limit width := ih limit smaller
        have certified := SourceCurrentAllocatedNativeCodeProgress.node_certified source facts holds request scope complete state
          valid.native.machine ready growth history
        exact code_of_bodies source holds limit bodies (compileNode request) state _
          certified.1 certified.2.1 certified.2.2.1 valid certified.2.2.2 growth history active ranges
      · intro request scope complete smaller state valid ready growth history active ranges
        let limit := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete
        have bodies : Bodies source holds limit width := ih limit smaller
        obtain ⟨code, operations, one, currentGood, operationGrowth, fields, safe, operands, below⟩ :=
          SourceCurrentAllocatedNativePhysicalCompletion.body_prefix source facts holds request scope complete state valid ready
        let current : Checked width := {state with operations := operations}
        have afterRanges := ranges.after_step _ _ _ _ one
        have returned := code_of_bodies source holds limit bodies code current _ safe operands below currentGood fields
          growth history active afterRanges
        exact before_step _ _ state current _ valid trivial ⟨ready, fun _ => trivial⟩ one returned

/-- Strong independent request descent discharges both recursive body families internally. -/
theorem code_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (code : Code Symbol Guard A)
    (state : Checked width) (post : Machine Symbol Guard → A → Prop)
    (safe : Safe code state.native.machine post)
    (operands : SourceCurrentAllocatedNativeCodeProgress.Operands code state.native.machine)
    (below : Below source holds bound code state.native.machine) (valid : Good state)
    (fields : CodeFields state.operations code)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds bound state.native) (ranges : WordRanges (.code code) state) :
    Returned (.code code) state post :=
  code_of_bodies source holds bound (all_bodies source facts holds bound) code state post
    safe operands below valid fields growth history active ranges

/-- An actual original node body has a complete physical trace at its independent request bound. -/
theorem node_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request))
    (state : Checked width) (valid : Good state) (ready : NodeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete) state.native)
    (ranges : WordRanges (.code (compileNode request)) state) :
    Returned (.code (compileNode request)) state (fun after value => Available after.heap value) := by
  exact (all_bodies source facts holds
    (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete + 1)).nodes
    request scope complete (Nat.lt_succ_self _) state valid ready growth history active ranges

/-- The actual checked edge body completes, including its real rejected-child skip. -/
theorem edge_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (state : Checked width) (valid : Good state) (ready : EdgeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete) state.native)
    (ranges : WordRanges (.edgeBody request .pure) state) :
    Returned (.edgeBody request .pure) state (fun after value => EdgeResident after.heap value) := by
  exact (all_bodies source facts holds
    (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete + 1)).edges
    request scope complete (Nat.lt_succ_self _) state valid ready growth history active ranges

/-- An actual node call, including lookup and demand, has a derived finite physical return. -/
theorem request_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request))
    (state : Checked width) (valid : Good state) (ready : NodeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete + 1) state.native)
    (ranges : WordRanges (.code (requestNode request.domain request.left request.right)) state) :
    Returned (.code (requestNode request.domain request.left request.right)) state (fun after value => Available after.heap value) := by
  apply code_complete source facts holds
    (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete + 1)
    _ state _ (safe_requestNode _ _ _ _ ready)
    ⟨ready, fun _ _ _ _ _ => trivial⟩
    (below_requestNode source holds _ request state.native.machine ⟨scope, complete, Nat.lt_succ_self _⟩)
    valid (fun _ => trivial) growth history active ranges

/-- Closed original roots derive the schedule bound and complete from an idle physical cache. -/
theorem initial_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (state : Checked width) (valid : Good state)
    (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.native.machine.heap left) (rightAvailable : Available state.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state value after
        (fun final value => Available final.heap value) ∧ SourceRecursiveIntersectionNative.Idle after.native := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have facts := valid.native.machine.1
  have complete : Completes (view state.native.machine.heap holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete state.native.machine.heap facts holds left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
  have ready : NodeReady state.native.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  obtain ⟨fuel, value, after, receipt⟩ := request_complete state.native.machine.heap facts holds request
    (initial_scope state.native.machine.heap left right leftOriginal rightOriginal leftAvailable rightAvailable)
    complete state valid ready (grows_refl _) (extends_refl _)
    (idle.active _ holds _ state.native) ranges
  have afterIdle := SourceCurrentAllocatedNativeRunning.done_idle (fuel + 1) _ state after value
    (by intro value; trivial) valid.native.shape idle receipt.done
  exact ⟨fuel, value, after, receipt, afterIdle⟩

end MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
