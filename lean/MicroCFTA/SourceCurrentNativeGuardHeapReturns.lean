import MicroCFTA.SourceCurrentNativeOperationHeap
import MicroCFTA.SourceCurrentConstrainedCapNativeGuardHeap

/-!
# Causal guard heaps through range-free native returns

Actual completed calls derive every intermediate physical state. The proof
retains body-to-probe guard observations for an arbitrary predicate. It does
not assert that all guards in a returned value satisfy that predicate.
-/
namespace MicroCFTA.SourceCurrentNativeGuardHeapReturns
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Good" => SourceCurrentNativeOperationHeap.Good
local notation "Cells" => SourceCurrentNativeOperationInvariants.Cells
local notation "Operands" => SourceCurrentAllocatedNativeCodeProgress.Operands
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Heap" => SourceCurrentConstrainedCapGuardHeap.Heap
variable {width : Nat}

private theorem replace_native {state : Checked width} (good : Good state)
    (native : Native width Symbol Guard) (valid : Cells native)
    (same : native.machine = state.native.machine) : Good ⟨native,state.operations⟩ :=
  ⟨valid,same.symm ▸ good.heap,good.operations,same.symm ▸ good.fields,
    same.symm ▸ good.semantic,same.symm ▸ good.costs⟩

private theorem lookupNode_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    :
    Cells (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using valid
  | some value =>
      simp only [lookupNode, key]
      exact ⟨valid.machine, FlatMemoThunk.lookup_valid value request state.nodes _ _ valid.nodes
        trivial ⟨ready, trivial⟩, valid.edges⟩

/-- Edge publication retains complete current rows. -/
private theorem lookupEdge_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    :
    Cells (lookupEdge width request state).2 :=
  ⟨valid.machine, valid.nodes, FlatMemoThunk.lookup_valid _ request state.edges _ _ valid.edges
    trivial ⟨ready, trivial⟩⟩

/-- Node demand retains every original input and returned availability. -/
private theorem demandNode_valid
    (state : Native width Symbol Guard) (valid : Cells state) (handle : Nat) :
    Cells (demandNode handle state).2 := by
  cases stored : state.nodes.cells handle with
  | none => simpa only [demandNode, FlatMemoThunk.demand, stored] using valid
  | some cell =>
      have good := valid.nodes.checked handle cell stored
      cases cell with
      | mk request status =>
          cases status with
          | evaluating | returned value => simpa only [demandNode, FlatMemoThunk.demand, stored] using valid
          | suspended =>
              simp only [demandNode, FlatMemoThunk.demand, stored]
              exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle .evaluating state.nodes _ _
                valid.nodes _ stored ⟨good.1, trivial⟩, valid.edges⟩

/-- Edge demand retains both native families and every returned row residency. -/
private theorem demandEdge_valid
    (state : Native width Symbol Guard) (valid : Cells state) (handle : Nat) :
    Cells (demandEdge handle state).2 := by
  cases stored : state.edges.cells handle with
  | none => simpa only [demandEdge, FlatMemoThunk.demand, stored] using valid
  | some cell =>
      have good := valid.edges.checked handle cell stored
      cases cell with
      | mk request status =>
          cases status with
          | evaluating | returned value => simpa only [demandEdge, FlatMemoThunk.demand, stored] using valid
          | suspended =>
              simp only [demandEdge, FlatMemoThunk.demand, stored]
              exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle .evaluating state.edges _ _
                valid.edges _ stored ⟨good.1, trivial⟩⟩


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem step_after {control next : Control A} {state after final : Checked width} {value : A}
    (one : step control state = .yielded next after)
    (actual : Steps (fuel+1) control state (.code (.pure value)) final) :
    Steps fuel next after (.code (.pure value)) final := by
  obtain ⟨rest,middle,observed,tail⟩ := steps_succ fuel _ _ _ _ actual
  obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (one.symm.trans observed)
  exact tail

private theorem finish_node_heap {count : Nat} (handle : Nat) (result value : Value Symbol Guard)
    (before after : Checked width)
    (actual : Steps count (.code (.finishNode handle result (.pure result))) before (.code (.pure value)) after) :
    after.native.machine.heap = before.native.machine.heap := by
  cases actual with
  | cons _ _ _ _ _ _ fuel one tail =>
      have expected : step (.code (.finishNode handle result (.pure result))) before =
          .yielded (.code (.pure result)) ⟨finishNode handle result before.native,before.operations⟩ := rfl
      obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (one.symm.trans expected)
      rw [←(pure_trace fuel result value _ after tail).2.2]
      rfl

private theorem finish_edge_heap {count : Nat} (handle : Nat) (result value : EdgeValue Symbol Guard)
    (before after : Checked width)
    (actual : Steps count (.code (.finishEdge handle result (.pure result))) before (.code (.pure value)) after) :
    after.native.machine.heap = before.native.machine.heap := by
  cases actual with
  | cons _ _ _ _ _ _ fuel one tail =>
      have expected : step (.code (.finishEdge handle result (.pure result))) before =
          .yielded (.code (.pure result)) ⟨finishEdge handle result before.native,before.operations⟩ := rfl
      obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (one.symm.trans expected)
      rw [←(pure_trace fuel result value _ after tail).2.2]
      rfl

private def CodeAt (annotation : Guard → Prop) (count : Nat) : Prop :=
  ∀ {A : Type} (program : Code Symbol Guard A) (before after : Checked width) (value : A)
    (post : Machine Symbol Guard → A → Prop),
    Steps count (.code program) before (.code (.pure value)) after → Good before →
    Safe program before.native.machine post → Operands program before.native.machine →
    CodeFields before.operations program → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

private def BodyAt (annotation : Guard → Prop) (count : Nat) : Prop :=
  ∀ (request : EdgeRequest Symbol Guard) (before after : Checked width) (value : EdgeValue Symbol Guard),
    Steps count (.edgeBody request .pure) before (.code (.pure value)) after → Good before →
    EdgeReady before.native.machine request → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

private theorem node_pure (annotation : Guard → Prop) (count : Nat)
    (ih : ∀ smaller, smaller < count+1 → CodeAt (width := width) annotation smaller)
    (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (actual : Steps (count+1) (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after)
    (good : Good before) (ready : NodeReady before.native.machine request) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  have chosenGood := lookupNode_valid before.native good.native request ready
  cases selected : lookupNode width request before.native with
  | mk selection chosen =>
    simp only [selected] at chosenGood
    cases selection with
    | direct captured =>
      obtain ⟨same,retained⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request captured before.native chosen selected
      subst captured
      subst chosen
      have one : step (.code (requestNode request.domain request.left request.right)) before =
          .yielded (.code ((compileNode request).bind .pure)) before := by
        simp only [requestNode,step,SourceRecursiveIntersectionNative.step,selected,lift]
      obtain ⟨inner,outer,result,middle,total,body,rest⟩ := steps_bind_inverse count (.code (compileNode request)) .pure before after value (step_after one actual)
      have retained := ih inner (by omega) (compileNode request) before middle result _ body good
        (compileNode_safe request before.native.machine good.native.machine ready)
        (SourceCurrentAllocatedNativeCodeProgress.compileNode_operands request before.native.machine good.native.machine ready)
        (SourceCurrentAllocatedNativeCodeFields.compileNode_fields _ request) heap
      rw [←(pure_trace outer result value middle after rest).2.2]
      exact retained
    | memoized handle =>
      have chosenMachine : chosen.machine = before.native.machine := by
        simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request before.native
      have currentGood := demandNode_valid chosen chosenGood handle
      cases demanded : demandNode handle chosen with
      | mk observation current =>
        simp only [demanded] at currentGood
        have currentMachine : current.machine = before.native.machine := by
          simpa only [demanded] using (SourceRecursiveIntersectionNative.demandNode_machine handle chosen).trans chosenMachine
        cases observation with
        | absent | busy =>
          obtain ⟨rest,middle,one,tail⟩ := steps_succ count _ _ _ _ actual
          simp only [requestNode,step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] at one
          cases one
        | ready result =>
          have one : step (.code (requestNode request.domain request.left request.right)) before =
              .yielded (.code (.pure result)) ⟨current,before.operations⟩ := by
            simp only [requestNode,step,SourceRecursiveIntersectionNative.step,selected,demanded,lift]
          rw [←(pure_trace count result value _ after (step_after one actual)).2.2,currentMachine]
          exact heap
        | evaluate captured =>
          have one : step (.code (requestNode request.domain request.left request.right)) before =
              .yielded (.code ((compileNode captured).bind (fun result => .finishNode handle result (.pure result)))) ⟨current,before.operations⟩ := by
            simp only [requestNode,step,SourceRecursiveIntersectionNative.step,selected,demanded,lift]
          have running := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen current captured demanded).2
          have capturedReady := (currentGood.nodes.checked handle _ running).1
          obtain ⟨inner,outer,result,middle,total,body,rest⟩ := steps_bind_inverse count (.code (compileNode captured))
            (fun result => .finishNode handle result (.pure result)) ⟨current,before.operations⟩ after value (step_after one actual)
          have retained := ih inner (by omega) (compileNode captured) _ middle result _ body
            (replace_native good current currentGood currentMachine)
            (compileNode_safe captured current.machine currentGood.machine capturedReady)
            (SourceCurrentAllocatedNativeCodeProgress.compileNode_operands captured current.machine currentGood.machine capturedReady)
            (SourceCurrentAllocatedNativeCodeFields.compileNode_fields _ captured) (by simpa only [currentMachine] using heap)
          rw [finish_node_heap handle result value middle after rest]
          exact retained

private theorem body_part (annotation : Guard → Prop) (count : Nat)
    (ih : ∀ smaller, smaller < count+1 → CodeAt (width := width) annotation smaller) : BodyAt (width := width) annotation (count+1) := by
  intro request before after value actual good ready heap
  obtain ⟨program,operations,one,valid,growth,retained,fields⟩ :=
    SourceCurrentAllocatedNativeFieldClosure.body_complete request .pure before good.operations good.fields ready (fun _ => trivial)
  have certified := SourceCurrentAllocatedNativeCodeProgress.body_certified request before {before with operations := operations}
    program good.native.machine ready one
  exact ih count (by omega) program {before with operations := operations} after value _ (step_after (control := .edgeBody request .pure) one actual)
    ⟨good.native,good.heap,valid,retained,good.semantic,good.costs⟩ certified.1 certified.2 fields heap

private theorem edge_pure (annotation : Guard → Prop) (count : Nat)
    (bodyIH : ∀ smaller, smaller < count+1 → BodyAt (width := width) annotation smaller)
    (request : EdgeRequest Symbol Guard) (before after : Checked width) (value : EdgeValue Symbol Guard)
    (actual : Steps (count+1) (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after)
    (good : Good before) (ready : EdgeReady before.native.machine request) (heap : Heap annotation before.native.machine.heap) :
    Heap annotation after.native.machine.heap := by
  have chosenGood := lookupEdge_valid before.native good.native request ready
  cases selected : lookupEdge width request before.native with
  | mk handle chosen =>
    simp only [selected] at chosenGood
    have chosenMachine : chosen.machine = before.native.machine := by
      simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
    have currentGood := demandEdge_valid chosen chosenGood handle
    cases demanded : demandEdge handle chosen with
    | mk observation current =>
      simp only [demanded] at currentGood
      have currentMachine : current.machine = before.native.machine := by
        simpa only [demanded] using (SourceRecursiveIntersectionNative.demandEdge_machine handle chosen).trans chosenMachine
      cases observation with
      | absent | busy =>
        obtain ⟨rest,middle,one,tail⟩ := steps_succ count _ _ _ _ actual
        simp only [requestEdge,step,selected,demanded] at one
        cases one
      | ready result =>
        have one : step (.code (requestEdge request.domain request.left request.right)) before =
            .yielded (.code (.pure result)) ⟨current,before.operations⟩ := by
          simp only [requestEdge,step,selected,demanded]
        rw [←(pure_trace count result value _ after (step_after one actual)).2.2,currentMachine]
        exact heap
      | evaluate captured =>
        have one : step (.code (requestEdge request.domain request.left request.right)) before =
            .yielded (.edgeBody captured (fun result => .finishEdge handle result (.pure result))) ⟨current,before.operations⟩ := by
          simp only [requestEdge,step,selected,demanded]
        have running := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen current captured demanded).2
        have capturedReady := (currentGood.edges.checked handle _ running).1
        obtain ⟨inner,outer,result,middle,total,body,rest⟩ := steps_bind_inverse count (.edgeBody captured .pure)
          (fun result => .finishEdge handle result (.pure result)) ⟨current,before.operations⟩ after value (step_after one actual)
        have retained := bodyIH inner (by omega) captured _ middle result body
          (replace_native good current currentGood currentMachine) capturedReady (by simpa only [currentMachine] using heap)
        rw [finish_edge_heap handle result value middle after rest]
        exact retained

private theorem code_part (annotation : Guard → Prop) (count : Nat)
    (ih : ∀ smaller, smaller < count+1 → CodeAt (width := width) annotation smaller)
    (bodyIH : ∀ smaller, smaller < count+1 → BodyAt (width := width) annotation smaller) : CodeAt (width := width) annotation (count+1) := by
  intro A program before after value post actual good safe operands fields heap
  cases program with
  | pure original => have impossible := (pure_trace (count+1) original value before after actual).1; omega
  | fail failure => obtain ⟨rest,middle,one,tail⟩ := steps_succ count _ _ _ _ actual; cases one
  | finishNode | finishEdge => cases safe
  | node request next =>
    obtain ⟨inner,outer,result,middle,total,first,rest⟩ := steps_bind_inverse (count+1)
      (.code (requestNode request.domain request.left request.right)) next before after value actual
    cases inner with
    | zero => have impossible := (steps_zero _ _ _ _ first).1; cases impossible
    | succ inner =>
      have retained := node_pure annotation inner (fun smaller below => ih smaller (by omega)) request before middle result first good safe.1 heap
      have built := SourceCurrentNativeOperationHeap.node (inner+2) request before middle result good safe.1 (trace_done _ _ _ _ _ first)
      exact ih outer (by omega) (next result) middle after value post rest built.1
        (safe.2 result middle.native.machine built.1.native.machine built.2.1 built.2.2.2.2)
        (operands.2 result middle.native.machine built.1.native.machine built.2.1 built.2.2.2.2)
        (SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (fields result) built.2.2.2.1) retained
  | edge request next =>
    obtain ⟨inner,outer,result,middle,total,first,rest⟩ := steps_bind_inverse (count+1)
      (.code (requestEdge request.domain request.left request.right)) next before after value actual
    cases inner with
    | zero => have impossible := (steps_zero _ _ _ _ first).1; cases impossible
    | succ inner =>
      have retained := edge_pure annotation inner (fun smaller below => bodyIH smaller (by omega)) request before middle result first good safe.1 heap
      have built := SourceCurrentNativeOperationHeap.edge (inner+2) request before middle result good safe.1 (trace_done _ _ _ _ _ first)
      exact ih outer (by omega) (next result) middle after value post rest built.1
        (safe.2 result middle.native.machine built.1.native.machine built.2.1 built.2.2.2.2)
        (operands.2 result middle.native.machine built.1.native.machine built.2.1 built.2.2.2.2)
        (SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (fields result) built.2.2.2.1) retained
  | work job next =>
    let made := run job before.native.machine.heap
    let machine := {before.native.machine with heap := made.2}
    let middle : Checked width := ⟨advance before.native machine,before.operations⟩
    have one : step (.code (.work job next)) before = .yielded (.code (next made.1)) middle := rfl
    have done : SourceRecursiveIntersectionKernel.work job before.native.machine = .done made.1 machine := rfl
    have built := SourceCurrentNativeOperationHeap.code 2 (.work job .pure) before middle made.1 (fun _ _ => True) good
      ⟨safe.1,safe.2.1,fun _ _ _ => trivial⟩ ⟨operands.1,fun _ _ _ => trivial⟩ ⟨fields.1,fun _ => trivial⟩ rfl
    exact ih count (by omega) (next made.1) middle after value post (step_after one actual) built.1
      (safe.2.2 made.1 machine done) (operands.2 made.1 machine done) (fields.2 made.1)
      (SourceCurrentConstrainedCapNativeGuardHeap.work_heap annotation job _ operands.1 heap)
  | enter domain left right first second next =>
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second
    let machine := {before.native.machine with domains := entered.2}
    let middle : Checked width := ⟨advance before.native machine,before.operations⟩
    have one : step (.code (.enter domain left right first second next)) before = .yielded (.code (next entered.1)) middle := rfl
    have built := SourceCurrentNativeOperationHeap.code 2 (.enter domain left right first second .pure) before middle entered.1 (fun _ _ => True) good
      ⟨safe.1,safe.2.1,trivial⟩ ⟨operands.1,operands.2.1,operands.2.2.1,trivial⟩ (fun _ => trivial) rfl
    exact ih count (by omega) (next entered.1) middle after value post (step_after one actual) built.1 safe.2.2 operands.2.2.2 (fields entered.1) heap
  | read name next =>
    have one : step (.code (.read name next)) before = .yielded (.code (next (SourcePreparedSharedRows.read before.native.machine.heap name))) before := rfl
    exact ih count (by omega) _ before after value post (step_after one actual) good safe operands (fields _) heap
  | optionalBinder pair body next =>
    have retained := SourceCurrentConstrainedCapGuardNative.optional_heap annotation pair body _ good.heap.semantic operands.1 heap
    cases called : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
    | pending key stopped =>
      obtain ⟨rest,middle,one,tail⟩ := steps_succ count _ _ _ _ actual
      simp only [step,SourceRecursiveIntersectionNative.step,called,lift] at one
      cases one
    | done result stopped =>
      let machine := {before.native.machine with heap := stopped}
      let middle : Checked width := ⟨advance before.native machine,before.operations⟩
      have done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap) before.native.machine = .done result machine := by rw [called]; rfl
      have one : step (.code (.optionalBinder pair body next)) before = .yielded (.code (next result)) middle := by
        simp only [step,SourceRecursiveIntersectionNative.step,called,lift]; rfl
      have numeric : execute 2 (.code (.optionalBinder pair body .pure)) before = .done result middle := by
        simp only [SourceEqualityNativeDemand.execute,step,SourceRecursiveIntersectionNative.step,called,lift]; rfl
      have built := SourceCurrentNativeOperationHeap.code 2 (.optionalBinder pair body .pure) before middle result (fun _ _ => True) good
        ⟨safe.1,safe.2.1,fun _ _ _ => trivial⟩ ⟨operands.1,fun _ _ _ => trivial⟩ (fun _ => trivial) numeric
      have guards : Heap annotation stopped := by simpa only [called,InternedNestedConstruction.Outcome.state] using retained
      exact ih count (by omega) (next result) middle after value post (step_after one actual) built.1
        (safe.2.2 result machine done) (operands.2 result machine done) (fields result) guards

private theorem all_done (annotation : Guard → Prop) (count : Nat) :
    CodeAt (width := width) annotation count ∧ BodyAt (width := width) annotation count := by
  induction count using Nat.strongRecOn with
  | ind count ih =>
    cases count with
    | zero =>
      constructor
      · intro A program before after value post actual good safe operands fields heap
        obtain ⟨same,rfl⟩ := steps_zero _ _ _ _ actual
        exact heap
      · intro request before after value actual good ready heap
        have impossible := (steps_zero _ _ _ _ actual).1
        cases impossible
    | succ count =>
      exact ⟨code_part annotation count (fun smaller below => (ih smaller below).1) (fun smaller below => (ih smaller below).2),
        body_part annotation count (fun smaller below => (ih smaller below).1)⟩

/-- An actual completed source program retains causal guard profiles without reached-input assumptions. -/
theorem code (annotation : Guard → Prop) (fuel : Nat) (program : Code Symbol Guard A)
    (before after : Checked width) (value : A) (post : Machine Symbol Guard → A → Prop)
    (good : Good before) (heap : Heap annotation before.native.machine.heap)
    (safe : Safe program before.native.machine post) (operands : Operands program before.native.machine)
    (fields : CodeFields before.operations program)
    (actual : execute fuel (.code program) before = .done value after) : Heap annotation after.native.machine.heap := by
  obtain ⟨count,below,trace⟩ := done_trace fuel (.code program) before after value actual
  exact (all_done annotation count).1 program before after value post trace good safe operands fields heap

/-- A completed node request derives its causal guard heap from its initial physical operands. -/
theorem node (annotation : Guard → Prop) (fuel : Nat) (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard) (good : Good before)
    (heap : Heap annotation before.native.machine.heap) (ready : NodeReady before.native.machine request)
    (actual : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done value after) :
    Heap annotation after.native.machine.heap :=
  code annotation fuel _ before after value _ good heap
    (safe_requestNode request.domain request.left request.right before.native.machine ready)
    ⟨ready,fun _ _ _ _ _ => trivial⟩ (fun _ => trivial) actual

/-- A completed row request retains causal guard profiles without key-range or semantic-cell premises. -/
theorem edge (annotation : Guard → Prop) (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (value : EdgeValue Symbol Guard) (good : Good before)
    (heap : Heap annotation before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (actual : execute fuel (.code (requestEdge request.domain request.left request.right)) before = .done value after) :
    Heap annotation after.native.machine.heap :=
  code annotation fuel _ before after value _ good heap
    (safe_requestEdge request.domain request.left request.right before.native.machine ready)
    ⟨ready,fun _ _ _ _ _ => trivial⟩ (fun _ => trivial) actual

end MicroCFTA.SourceCurrentNativeGuardHeapReturns
