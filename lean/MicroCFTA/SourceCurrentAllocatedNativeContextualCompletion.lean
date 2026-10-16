import MicroCFTA.SourceCurrentAllocatedNativeContextualCode
import MicroCFTA.SourceCurrentAllocatedNativeContextExecution
import MicroCFTA.SourceCurrentAllocatedNativeContextualCertificates
import MicroCFTA.SourceCurrentAllocatedNativeContextualNodeCertificates

/-!
# Joint contextual execution of actual checked code

The semantic proof follows the same protected physical traces. A request
finishes only after its local child laws derive its own returned law.
The independent request bound discharges recursive body obligations.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "ActiveAbove" => SourceRecursiveIntersectionNative.ActiveAbove
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {A B : Type} {width fuel : Nat}
variable {semanticView : IntersectSchedule.View Symbol} {model : IntersectSchedule.InputMeaning semanticView}
  {ranked : IntersectSchedule.RankedInput semanticView model.valid} {semanticHolds : Guard → Term Symbol → Bool}
local notation "Contextual" => SourceCurrentAllocatedNativeContextCache.Contextual semanticView model ranked semanticHolds
local notation "NodeLaw" => SourceCurrentAllocatedNativeContextCache.NodeLaw semanticView model ranked semanticHolds
local notation "EdgeLaw" => SourceCurrentAllocatedNativeContextCache.EdgeLaw semanticView model ranked semanticHolds
local notation "Certified" => SourceCurrentAllocatedNativeContextualCode.Certified semanticView model ranked semanticHolds

/-- A returned law refers to the same actual physical trace and machine. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (before : Checked width) (value : A) (after : Checked width)
    (post semanticPost : Machine Symbol Guard → A → Prop) : Prop
    extends SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel control before value after post where
  contextual : Contextual after.native
  semantic : SemanticReady after.native.machine.heap
  law : semanticPost after.native.machine value

/-- Joint completion returns one physical result and its contextual law. -/
def Returned [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (before : Checked width) (post semanticPost : Machine Symbol Guard → A → Prop) : Prop :=
  ∃ fuel value after, Receipt (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) fuel control before value after post semanticPost

/-- The joint receipt completes the literal checked interpreter. -/
theorem Receipt.done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {control : Control A} {before after : Checked width} {value : A} {post semanticPost : Machine Symbol Guard → A → Prop}
    (receipt : Receipt (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) fuel control before value after post semanticPost) :
    execute (fuel + 1) control before = .done value after := receipt.toReceipt.done

private theorem operations_trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) :
    SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations, Cache.extends_trans first.descents second.descents⟩

private theorem before_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control A) (state current : Checked width) (post : Machine Symbol Guard → A → Prop) (semanticPost : Machine Symbol Guard → A → Prop)
    (valid : Good state) (inputs : Inputs control state) (fields : Fields control state)
    (one : step control state = .yielded next current) (later : Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) next current post semanticPost) :
    Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) control state post semanticPost := by
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control state valid inputs fields
  have currentEffects : Good current ∧ Extension state.native.machine current.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap current.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations current.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (.yielded next current) := by
    simpa only [one, Outcome.state] using checked
  obtain ⟨fuel, value, after, receipt⟩ := later
  exact ⟨fuel + 1, value, after, ⟨⟨.cons _ _ _ _ _ _ _ inputs one receipt.trace, receipt.good,
    currentEffects.2.1.trans receipt.extension, currentEffects.2.2.1.trans receipt.keeps,
    operations_trans currentEffects.2.2.2.1 receipt.operations, receipt.result⟩, receipt.contextual, receipt.semantic, receipt.law⟩⟩


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

private theorem yielded_context [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control A) (state current : Checked width) (contextual : Contextual state.native)
    (localLaw : SourceCurrentAllocatedNativeContextExecution.FinishLaw semanticView model ranked semanticHolds control state)
    (one : step control state = .yielded next current) : Contextual current.native := by
  have retained := SourceCurrentAllocatedNativeContextExecution.step_contextual semanticView model ranked semanticHolds
    control state contextual localLaw
  simpa only [one, Outcome.state] using retained

private theorem yielded_semantic [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control A) (state current : Checked width) (semantic : SemanticReady state.native.machine.heap)
    (inputs : Inputs control state) (one : step control state = .yielded next current) :
    SemanticReady current.native.machine.heap := by
  have retained := SourceCurrentAllocatedNativeSemanticHeap.step_semantic control state semantic
    (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control state inputs)
  simpa only [one, Outcome.state] using retained

private theorem join [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (state current : Checked width) (value : A) (fuel : Nat)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop) (semanticPost : Machine Symbol Guard → B → Prop)
    (bodyPost : Machine Symbol Guard → A → Prop) (body : Receipt (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) fuel control state value current intermediate bodyPost) (next : A → Code Symbol Guard B)
    (later : Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.code (next value)) current post semanticPost) : Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (control.bind next) state post semanticPost := by
  obtain ⟨count, output, after, receipt⟩ := later
  exact ⟨fuel + count, output, after,
    ⟨⟨(body.trace.bind next).trans receipt.trace, receipt.good, body.extension.trans receipt.extension,
      body.keeps.trans receipt.keeps, operations_trans body.operations receipt.operations, receipt.result⟩,
      receipt.contextual, receipt.semantic, receipt.law⟩⟩

private structure Bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound width : Nat) : Prop where
  nodes : ∀ request : NodeRequest Symbol Guard, NodeScope source request →
    ∀ complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request),
    requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete < bound →
    ∀ state : Checked width, Good state → Contextual state.native → SemanticReady state.native.machine.heap → NodeReady state.native.machine request →
    Grows source state.native.machine.heap → Extends source.nodes.issued state.native.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete) state.native →
    WordRanges (.code (compileNode request)) state →
    Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.code (compileNode request)) state (fun after value => Available after.heap value) (fun _ value => NodeLaw request value)
  edges : ∀ request : EdgeRequest Symbol Guard, EdgeScope source request →
    ∀ complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request),
    requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete < bound →
    ∀ state : Checked width, Good state → Contextual state.native → SemanticReady state.native.machine.heap →
    request.left.entry.key.symbol = request.right.entry.key.symbol → EdgeReady state.native.machine request →
    Grows source state.native.machine.heap → Extends source.nodes.issued state.native.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete) state.native →
    WordRanges (.edgeBody request .pure) state →
    Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.edgeBody request .pure) state (fun after value => EdgeResident after.heap value) (fun _ value => EdgeLaw request value)

private theorem node_of_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (bodies : Bodies (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) source holds bound width) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (state : Checked width) (post : Machine Symbol Guard → A → Prop) (semanticPost : Machine Symbol Guard → A → Prop)
    (valid : Good state) (contextual : Contextual state.native) (semantic : SemanticReady state.native.machine.heap) (ready : NodeReady state.native.machine request) (below : NodeBelow source holds bound request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds bound state.native) (ranges : WordRanges (.code (.node request next)) state)
    (fields : ∀ value, CodeFields state.operations (next value))
    (later : ∀ (value : Value Symbol Guard) (after : Checked width), Good after → Contextual after.native → SemanticReady after.native.machine.heap →
      Extension state.native.machine after.native.machine → NodeLaw request value →
      Available after.native.machine.heap value → ActiveAbove (view source holds) holds bound after.native →
      WordRanges (.code (next value)) after → CodeFields after.operations (next value) →
      Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.code (next value)) after post semanticPost) : Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.code (.node request next)) state post semanticPost := by
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
      obtain ⟨fuel, value, current, body⟩ := bodies.nodes request scope complete smaller state valid contextual semantic ready growth history
        (active.weaken _ holds bound limit (Nat.le_of_lt smaller) _) bodyRanges
      have afterActive := active.running_before _ holds bound state.native current.native
        (SourceCurrentAllocatedNativeRunning.trace_running_before fuel _ state current value body.trace.steps
          (compileNode_bodyCode request) valid.native.shape)
      have nextFields := SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations current.operations
        (next value) (fields value) body.operations
      have tail := later value current body.good body.contextual body.semantic body.extension body.law body.result afterActive
        (entered.after_body (.code (compileNode request)) next state current fuel value body.trace.steps) nextFields
      exact before_step _ _ state state post semanticPost valid inputs fields one (join _ state current value fuel _ post semanticPost _ body next tail)
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
          have semanticResult := SourceCurrentAllocatedNativeContextualPhysicalCache.node_observed_ready semanticView model ranked semanticHolds request state.native chosen current handle value
            valid.native contextual ready safe selected demanded
          have returned := SourceCurrentAllocatedNativePhysicalCache.node_ready request state.native chosen current handle value
            valid.native ready safe selected demanded
          let after : Checked width := ⟨current, state.operations⟩
          have one : step (.code (.node request next)) state = .yielded (.code (next value)) after := by
            simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, after]
          have afterGood := yielded_good _ _ state after valid inputs fields one
          have sameMachine : current.machine = state.native.machine := by rw [returned.2.1]; exact chosenMachine
          have physical : Extension state.native.machine current.machine := by rw [sameMachine]; exact .refl _
          have afterActive : ActiveAbove (view source holds) holds bound current := by rw [returned.2.1]; exact chosenActive
          exact before_step _ _ state after post semanticPost valid inputs fields one
            (later value after afterGood.1 semanticResult.2.1 (by simpa only [after, sameMachine] using semantic) physical semanticResult.1 returned.2.2 afterActive (ranges.after_step _ _ _ _ one) afterGood.2)
        | evaluate original =>
          have same := SourceCurrentAllocatedNativePhysicalCache.node_started request original state.native chosen current handle
            valid.native ready safe selected demanded
          subst original
          let start : Checked width := ⟨current, state.operations⟩
          let frame := fun value => Code.finishNode handle value (next value)
          have one : step (.code (.node request next)) state = .yielded (.code ((compileNode request).bind frame)) start := by
            simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, frame, start]
          have startGood := (yielded_good _ _ state start valid inputs fields one).1
          have startContext := yielded_context (.code (.node request next)) _ state start contextual trivial one
          have startSemantic := yielded_semantic _ _ state start semantic inputs one
          have sameMachine : current.machine = state.native.machine :=
            (show current.machine = chosen.machine from by
              simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_machine handle chosen).trans chosenMachine
          have startReady : NodeReady current.machine request := by rw [sameMachine]; exact ready
          have startActive := (chosenActive.weaken _ holds bound limit (Nat.le_of_lt smaller) _).startNode
            (view source holds) holds limit chosen current handle request demanded complete (Nat.le_refl _)
          have entered := ranges.after_step _ _ _ _ one
          have bodyRanges := entered.before_bind (.code (compileNode request)) frame start
          obtain ⟨fuel, value, middle, body⟩ := bodies.nodes request scope complete smaller start startGood startContext startSemantic startReady
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
          have finishedContext := SourceCurrentAllocatedNativeContextCache.finishNode_contextual semanticView model ranked semanticHolds
            middle.native handle request value body.contextual preserved.1 body.law
          have physical : Extension state.native.machine finished.native.machine := by
            change Extension state.native.machine middle.native.machine
            rw [← sameMachine]
            exact body.extension
          have afterActive := SourceCurrentAllocatedNativeRunning.node_finish_active (view source holds) holds bound
            fuel handle request chosen start middle value chosenActive demanded startGood.native.shape body.trace.steps
          have atFrame := entered.after_body (.code (compileNode request)) frame start middle fuel value body.trace.steps
          have tail := later value finished finishedGood.1 finishedContext body.semantic physical body.law body.result afterActive
            (atFrame.after_step _ _ _ _ finishStep) finishedGood.2
          have framed := before_step _ _ middle finished post semanticPost body.good finishInputs finishFields finishStep tail
          exact before_step _ _ state start post semanticPost valid inputs fields one
            (join _ start middle value fuel _ post semanticPost _ body frame framed)


private theorem edge_of_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (bodies : Bodies (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) source holds bound width) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (state : Checked width) (post : Machine Symbol Guard → A → Prop) (semanticPost : Machine Symbol Guard → A → Prop)
    (valid : Good state) (contextual : Contextual state.native) (semantic : SemanticReady state.native.machine.heap)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol) (ready : EdgeReady state.native.machine request) (below : EdgeBelow source holds bound request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds bound state.native) (ranges : WordRanges (.code (.edge request next)) state)
    (fields : ∀ value, CodeFields state.operations (next value))
    (later : ∀ (value : EdgeValue Symbol Guard) (after : Checked width), Good after → Contextual after.native → SemanticReady after.native.machine.heap →
      Extension state.native.machine after.native.machine → EdgeLaw request value →
      EdgeResident after.native.machine.heap value → ActiveAbove (view source holds) holds bound after.native →
      WordRanges (.code (next value)) after → CodeFields after.operations (next value) →
      Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.code (next value)) after post semanticPost) : Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.code (.edge request next)) state post semanticPost := by
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
        have semanticResult := SourceCurrentAllocatedNativeContextualPhysicalCache.edge_observed_ready semanticView model ranked semanticHolds request state.native chosen current handle value
          valid.native contextual ready words selected demanded
        have returned := SourceCurrentAllocatedNativePhysicalCache.edge_ready request state.native chosen current handle value
          valid.native ready words selected demanded
        let after : Checked width := ⟨current, state.operations⟩
        have one : step (.code (.edge request next)) state = .yielded (.code (next value)) after := by
          simp only [step, selected, demanded, after]
        have afterGood := yielded_good _ _ state after valid inputs fields one
        have sameMachine : current.machine = state.native.machine := by rw [returned.2.1]; exact chosenMachine
        have physical : Extension state.native.machine current.machine := by rw [sameMachine]; exact .refl _
        have afterActive : ActiveAbove (view source holds) holds bound current := by rw [returned.2.1]; exact chosenActive
        exact before_step _ _ state after post semanticPost valid inputs fields one
          (later value after afterGood.1 semanticResult.2.1 (by simpa only [after, sameMachine] using semantic) physical semanticResult.1 returned.2.2 afterActive (ranges.after_step _ _ _ _ one) afterGood.2)
      | evaluate original =>
        have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request original state.native chosen current handle
          valid.native ready words selected demanded
        subst original
        let start : Checked width := ⟨current, state.operations⟩
        let frame := fun value => Code.finishEdge handle value (next value)
        have one : step (.code (.edge request next)) state = .yielded (.edgeBody request frame) start := by
          simp only [step, selected, demanded, frame, start]
        have startGood := (yielded_good _ _ state start valid inputs fields one).1
        have startContext := yielded_context (.code (.edge request next)) _ state start contextual trivial one
        have startSemantic := yielded_semantic _ _ state start semantic inputs one
        have sameMachine : current.machine = state.native.machine :=
          (show current.machine = chosen.machine from by
            simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen).trans chosenMachine
        have startReady : EdgeReady current.machine request := by rw [sameMachine]; exact ready
        have startActive := (chosenActive.weaken _ holds bound limit (Nat.le_of_lt smaller) _).startEdge
          (view source holds) holds limit chosen current handle request demanded complete (Nat.le_refl _)
        have entered := ranges.after_step _ _ _ _ one
        have bodyRanges := entered.before_bind (.edgeBody request .pure) frame start
        obtain ⟨fuel, value, middle, body⟩ := bodies.edges request scope complete smaller start startGood startContext startSemantic symbols startReady
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
        have finishedContext := SourceCurrentAllocatedNativeContextCache.finishEdge_contextual semanticView model ranked semanticHolds
          middle.native handle request value body.contextual preserved.1 body.law
        have physical : Extension state.native.machine finished.native.machine := by
          change Extension state.native.machine middle.native.machine
          rw [← sameMachine]
          exact body.extension
        have afterActive := SourceCurrentAllocatedNativeRunning.edge_finish_active (view source holds) holds bound
          fuel handle request chosen start middle value chosenActive demanded startGood.native.shape body.trace.steps
        have atFrame := entered.after_body (.edgeBody request .pure) frame start middle fuel value body.trace.steps
        have tail := later value finished finishedGood.1 finishedContext body.semantic physical body.law body.result afterActive
          (atFrame.after_step _ _ _ _ finishStep) finishedGood.2
        have framed := before_step _ _ middle finished post semanticPost body.good finishInputs finishFields finishStep tail
        exact before_step _ _ state start post semanticPost valid inputs fields one
          (join _ start middle value fuel _ post semanticPost _ body frame framed)


private theorem code_of_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (bound : Nat) (bodies : Bodies (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) source holds bound width) (code : Code Symbol Guard A) :
    ∀ (state : Checked width) (post semanticPost : Machine Symbol Guard → A → Prop),
    Safe code state.native.machine post → SourceCurrentAllocatedNativeCodeProgress.Operands code state.native.machine →
    Below source holds bound code state.native.machine → Good state → Contextual state.native →
    SemanticReady state.native.machine.heap → Certified code state.native.machine semanticPost → CodeFields state.operations code →
    Grows source state.native.machine.heap → Extends source.nodes.issued state.native.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds bound state.native → WordRanges (.code code) state →
    Returned (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) (.code code) state post semanticPost := by
  induction code with
  | pure value =>
      intro state post semanticPost safe _ _ valid contextual semantic certificate _ _ _ _ _
      exact ⟨0, value, state, ⟨⟨.refl _ _, valid, .refl _, SourceEqualityRequiredCache.pure_keeps _ valid.heap,
        SourceEqualityConstraintMemoAllocation.grows_refl _, safe⟩, contextual, semantic, certificate⟩⟩
  | fail failure => intro _ _ _ _ _ impossible; cases impossible
  | work job next ih =>
      intro state post semanticPost safe operands below valid contextual semantic certificate fields growth history active ranges
      let actual := InternedConstructorTemplates.run job state.native.machine.heap
      let machine : Machine Symbol Guard := {state.native.machine with heap := actual.2}
      let after : Checked width := {state with native := advance state.native machine}
      have one : step (.code (.work job next)) state = .yielded (.code (next actual.1)) after := rfl
      have checked := yielded_good (.code (.work job next)) (.code (next actual.1)) state after valid operands.1 fields one
      have call : SourceRecursiveIntersectionKernel.work job state.native.machine = .done actual.1 machine := rfl
      have physical : Extension state.native.machine machine := safe.2.1
      have afterContext := yielded_context (.code (.work job next)) _ state after contextual trivial one
      have afterSemantic := yielded_semantic (.code (.work job next)) _ state after semantic operands.1 one
      exact before_step (.code (.work job next)) (.code (next actual.1)) state after post semanticPost valid operands.1 fields one
        (ih actual.1 after post semanticPost (safe.2.2 _ _ call) (operands.2 _ _ call) (below _ _ call)
          checked.1 afterContext afterSemantic (certificate _ _ call checked.1.native.machine physical afterSemantic)
          checked.2 (grows_trans growth physical.heap) (extends_trans history physical.history)
          (active.advance _ holds bound _ machine) (ranges.after_step _ _ _ _ one))
  | enter domain left right first second next ih =>
      intro state post semanticPost safe operands below valid contextual semantic certificate fields growth history active ranges
      let actual := SourceRecursiveIntersectionEnvironment.enter state.native.machine.domains domain.key left right first second
      let machine : Machine Symbol Guard := {state.native.machine with domains := actual.2}
      let after : Checked width := {state with native := advance state.native machine}
      have inputs : Inputs (.code (.enter domain left right first second next)) state :=
        ⟨operands.1, operands.2.1, operands.2.2.1⟩
      have one : step (.code (.enter domain left right first second next)) state = .yielded (.code (next actual.1)) after := rfl
      have checked := yielded_good _ _ state after valid inputs fields one
      have physical : Extension state.native.machine machine := safe.2.1
      have afterContext := yielded_context (.code (.enter domain left right first second next)) _ state after contextual trivial one
      exact before_step _ _ state after post semanticPost valid inputs fields one
        (ih actual.1 after post semanticPost safe.2.2 operands.2.2.2 below checked.1 afterContext semantic certificate.2.2 checked.2
          (grows_trans growth physical.heap) (extends_trans history physical.history)
          (active.advance _ holds bound _ machine) (ranges.after_step _ _ _ _ one))
  | read name next ih =>
      intro state post semanticPost safe operands below valid contextual semantic certificate fields growth history active ranges
      have one : step (.code (.read name next)) state =
          .yielded (.code (next (SourcePreparedSharedRows.read state.native.machine.heap name))) state := rfl
      exact before_step _ _ state state post semanticPost valid trivial fields one
        (ih _ state post semanticPost safe operands below valid contextual semantic certificate (fields _) growth history active
          (ranges.after_step _ _ _ _ one))
  | optionalBinder key body next ih =>
      intro state post semanticPost safe operands below valid contextual semantic certificate fields growth history active ranges
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
      have afterContext := yielded_context (.code (.optionalBinder key body next)) _ state after contextual trivial one
      have afterSemantic := yielded_semantic (.code (.optionalBinder key body next)) _ state after semantic operands.1 one
      exact before_step (.code (.optionalBinder key body next)) (.code (next value)) state after post semanticPost valid operands.1 fields one
        (ih value after post semanticPost (safe.2.2 _ _ call) (operands.2 _ _ call) (below _ _ call)
          checked.1 afterContext afterSemantic (certificate _ _ call checked.1.native.machine physical afterSemantic)
          checked.2 (grows_trans growth physical.heap) (extends_trans history physical.history)
          (active.advance _ holds bound _ machine) (ranges.after_step _ _ _ _ one))
  | node request next ih =>
      intro state post semanticPost safe operands below valid contextual semantic certificate fields growth history active ranges
      apply node_of_bodies source holds bound bodies request next state post semanticPost valid contextual semantic safe.1 below.1
        growth history active ranges fields
      intro value after afterGood afterContext afterSemantic physical law available afterActive afterRanges afterFields
      exact ih value after post semanticPost (safe.2 _ _ afterGood.native.machine physical available)
        (operands.2 _ _ afterGood.native.machine physical available) (below.2 _ _ afterGood.native.machine physical available)
        afterGood afterContext afterSemantic (certificate _ _ afterGood.native.machine physical afterSemantic available law)
        afterFields (grows_trans growth physical.heap) (extends_trans history physical.history) afterActive afterRanges
  | edge request next ih =>
      intro state post semanticPost safe operands below valid contextual semantic certificate fields growth history active ranges
      apply edge_of_bodies source holds bound bodies request next state post semanticPost valid contextual semantic certificate.1 safe.1 below.1
        growth history active ranges fields
      intro value after afterGood afterContext afterSemantic physical law available afterActive afterRanges afterFields
      exact ih value after post semanticPost (safe.2 _ _ afterGood.native.machine physical available)
        (operands.2 _ _ afterGood.native.machine physical available) (below.2 _ _ afterGood.native.machine physical available)
        afterGood afterContext afterSemantic (certificate.2 _ _ afterGood.native.machine physical afterSemantic available law)
        afterFields (grows_trans growth physical.heap) (extends_trans history physical.history) afterActive afterRanges
  | finishNode | finishEdge => intro _ _ _ _ _ impossible; cases impossible

private theorem all_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool)
    (certifiedNodes : ∀ (request : NodeRequest Symbol Guard), NodeScope source request →
      ∀ (state : Checked width), Good state → SemanticReady state.native.machine.heap → NodeReady state.native.machine request →
      Grows source state.native.machine.heap → Extends source.nodes.issued state.native.machine.heap.nodes.issued →
      Certified (compileNode request) state.native.machine (fun _ value => NodeLaw request value))
    (certifiedEdges : ∀ (request : EdgeRequest Symbol Guard), EdgeScope source request →
      ∀ (state : Checked width), Good state → SemanticReady state.native.machine.heap → EdgeReady state.native.machine request →
      request.left.entry.key.symbol = request.right.entry.key.symbol →
      ∀ (code : Code Symbol Guard (EdgeValue Symbol Guard)) (operations : SourceEqualityConstraintMemoAllocation.State),
      step (.edgeBody request .pure) state = .yielded (.code code) {state with operations := operations} →
      Certified code state.native.machine (fun _ value => EdgeLaw request value))
    (bound : Nat) : Bodies (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) source holds bound width := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      constructor
      · intro request scope complete smaller state valid contextual semantic ready growth history active ranges
        let limit := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete
        have bodies : Bodies (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) source holds limit width := ih limit smaller
        have certified := SourceCurrentAllocatedNativeCodeProgress.node_certified source facts holds request scope complete state
          valid.native.machine ready growth history
        exact code_of_bodies source holds limit bodies (compileNode request) state _ _
          certified.1 certified.2.1 certified.2.2.1 valid contextual semantic
          (certifiedNodes request scope state valid semantic ready growth history)
          certified.2.2.2 growth history active ranges
      · intro request scope complete smaller state valid contextual semantic symbols ready growth history active ranges
        let limit := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete
        have bodies : Bodies (semanticView := semanticView) (model := model) (ranked := ranked) (semanticHolds := semanticHolds) source holds limit width := ih limit smaller
        obtain ⟨code, operations, one, currentGood, operationGrowth, fields, safe, operands, below⟩ :=
          SourceCurrentAllocatedNativePhysicalCompletion.body_prefix source facts holds request scope complete state valid ready
        let current : Checked width := {state with operations := operations}
        have afterRanges := ranges.after_step _ _ _ _ one
        have returned := code_of_bodies source holds limit bodies code current _ _ safe operands below currentGood contextual semantic
          (certifiedEdges request scope state valid semantic ready symbols code operations one) fields growth history active afterRanges
        exact before_step _ _ state current _ _ valid trivial ⟨ready, fun _ => trivial⟩ one returned

private theorem source_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (bound : Nat) :
    Bodies (semanticView := view source (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
      (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
      source (SourceEqualityPCSGuard.holds formulas solver) bound width := by
  apply all_bodies source facts (SourceEqualityPCSGuard.holds formulas solver)
  · intro request scope state good semantic ready growth history
    exact SourceCurrentAllocatedNativeContextualNodeCertificates.node_certified source facts
      (SourceEqualityPCSGuard.holds formulas solver) inputModel inputRanked request scope state.native.machine
      good.native.machine semantic ready growth history
  · intro request _ state good semantic ready symbols code operations one
    exact SourceCurrentAllocatedNativeContextualCertificates.prefix_certified
      (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked formulas solver
      request state code operations good semantic ready symbols one

/-- Actual checked node bodies derive their own contextual law by strict request descent. -/
theorem node_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.nodeSemantic request))
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (semantic : SemanticReady state.native.machine.heap) (ready : NodeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceEqualityPCSGuard.holds formulas solver)
      (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.nodeSemantic request) complete) state.native)
    (ranges : WordRanges (.code (compileNode request)) state) :
    Returned (semanticView := view source (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
      (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
      (.code (compileNode request)) state (fun after value => Available after.heap value)
      (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
        (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) request value) := by
  exact (source_bodies source facts formulas solver inputModel inputRanked
    (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.nodeSemantic request) complete + 1)).nodes
    request scope complete (Nat.lt_succ_self _) state valid contextual semantic ready growth history active ranges

/-- Actual checked edge bodies derive rejection or ordered child laws before any finish. -/
theorem edge_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source (SourceEqualityPCSGuard.holds formulas solver))
      (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request))
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (semantic : SemanticReady state.native.machine.heap)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol) (ready : EdgeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceEqualityPCSGuard.holds formulas solver)
      (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver))
        (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request) complete) state.native)
    (ranges : WordRanges (.edgeBody request .pure) state) :
    Returned (semanticView := view source (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
      (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
      (.edgeBody request .pure) state (fun after value => EdgeResident after.heap value)
      (fun _ value => SourceCurrentAllocatedNativeContextCache.EdgeLaw
        (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) request value) := by
  exact (source_bodies source facts formulas solver inputModel inputRanked
    (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver))
      (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request) complete + 1)).edges
    request scope complete (Nat.lt_succ_self _) state valid contextual semantic symbols ready growth history active ranges

/-- Lookup, demand, and each protected finish return the same node law and native cache. -/
theorem request_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.nodeSemantic request))
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (semantic : SemanticReady state.native.machine.heap) (ready : NodeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceEqualityPCSGuard.holds formulas solver)
      (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.nodeSemantic request) complete + 1) state.native)
    (ranges : WordRanges (.code (requestNode request.domain request.left request.right)) state) :
    Returned (semanticView := view source (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
      (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
      (.code (requestNode request.domain request.left request.right)) state (fun after value => Available after.heap value)
      (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
        (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) request value) := by
  apply code_of_bodies source (SourceEqualityPCSGuard.holds formulas solver)
    (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.nodeSemantic request) complete + 1)
    (source_bodies source facts formulas solver inputModel inputRanked _) _ state _ _
    (safe_requestNode _ _ _ _ ready) ⟨ready, fun _ _ _ _ _ => trivial⟩
    (below_requestNode source (SourceEqualityPCSGuard.holds formulas solver) _ request state.native.machine ⟨scope, complete, Nat.lt_succ_self _⟩)
    valid contextual semantic (fun _ _ _ _ _ _ law => law) (fun _ => trivial) growth history active ranges

/-- Actual edge lookup, demand, and protected finish derive the requested edge law. -/
theorem edge_request_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request))
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (semantic : SemanticReady state.native.machine.heap)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol) (ready : EdgeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceEqualityPCSGuard.holds formulas solver)
      (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request) complete + 1) state.native)
    (ranges : WordRanges (.code (requestEdge request.domain request.left request.right)) state) :
    Returned (semanticView := view source (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
      (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
      (.code (requestEdge request.domain request.left request.right)) state (fun after value => EdgeResident after.heap value)
      (fun _ value => SourceCurrentAllocatedNativeContextCache.EdgeLaw
        (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) request value) := by
  apply code_of_bodies source (SourceEqualityPCSGuard.holds formulas solver)
    (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request) complete + 1)
    (source_bodies source facts formulas solver inputModel inputRanked _) _ state _ _
    (safe_requestEdge _ _ _ _ ready) ⟨ready, fun _ _ _ _ _ => trivial⟩
    (below_requestEdge source (SourceEqualityPCSGuard.holds formulas solver) _ request state.native.machine ⟨scope, complete, Nat.lt_succ_self _⟩)
    valid contextual semantic ⟨symbols, fun _ _ _ _ _ _ law => law⟩ (fun _ => trivial) growth history active ranges

/-- Idle original closed inputs derive their request bound and all contextual finishes. -/
theorem initial_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (state : Checked width) (valid : Good state)
    (inputModel : InputMeaning (view state.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view state.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view state.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.native.machine.heap left) (rightAvailable : Available state.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value after,
      Receipt (semanticView := view state.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view state.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver)
          ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧ SourceRecursiveIntersectionNative.Idle after.native := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have facts := valid.native.machine.1
  have complete : Completes (view state.native.machine.heap holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete state.native.machine.heap facts holds left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
  have ready : NodeReady state.native.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  obtain ⟨fuel, value, after, receipt⟩ := request_complete state.native.machine.heap facts formulas solver inputModel inputRanked request
    (initial_scope state.native.machine.heap left right leftOriginal rightOriginal leftAvailable rightAvailable)
    complete state valid contextual semantic ready (grows_refl _) (extends_refl _)
    (idle.active _ holds _ state.native) ranges
  have afterIdle := SourceCurrentAllocatedNativeRunning.done_idle (fuel + 1) _ state after value
    (by intro value; trivial) valid.native.shape idle receipt.done
  exact ⟨fuel, value, after, receipt, afterIdle⟩

/-- Cold closed inputs derive both fixed models and exact independent root language. -/
theorem cold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : Good (⟨initial width machine, operations⟩ : Checked width))
    (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (⟨initial width machine, operations⟩ : Checked width)) :
    ∃ (inputModel : InputMeaning (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)))
      (inputRanked : RankedInput (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
      (fuel : Nat) (value : Value Symbol Guard) (after : Checked width),
      Receipt (semanticView := view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) ⟨initial width machine, operations⟩ value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver)
          ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧
      ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  obtain ⟨inputModel, inputRanked, _, sourceLaw⟩ := SourceCurrentAllocatedNativeClosedReceipts.source_models machine.heap
    valid.native.machine.1 holds request leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have contextual := SourceCurrentAllocatedNativeContextCache.initial_contextual
    (view machine.heap holds) inputModel inputRanked holds width machine
  obtain ⟨fuel, value, after, receipt, idle⟩ := initial_complete formulas solver ⟨initial width machine, operations⟩ valid
    inputModel inputRanked contextual semantic (SourceRecursiveIntersectionNative.idle_initial machine)
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨inputModel, inputRanked, fuel, value, after, receipt, idle,
    (sourceLaw value receipt.law) rfl leftClosed rightClosed⟩

end MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion
