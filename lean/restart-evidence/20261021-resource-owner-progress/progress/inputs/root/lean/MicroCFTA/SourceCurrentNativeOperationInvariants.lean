import MicroCFTA.SourceCurrentAllocatedNativeCodeProgress
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion
import MicroCFTA.SourceCurrentOperationGrowth
import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# Equality-operation invariants from actual native returns

Physical native cells retain resident inputs and results. Their invariant
uses no machine word bound and no semantic result law. Actual completed
compiled calls derive their operation-cache invariants from initial fields.
-/
namespace MicroCFTA.SourceCurrentNativeOperationInvariants
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCache (NodeGood EdgeGood)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Operands" => SourceCurrentAllocatedNativeCodeProgress.Operands
local notation "Fields" => SourceCurrentConjunctionEquality.Fields
variable {width : Nat}
/-- Physical native cells retain available operands and results without a key-range law. -/
structure Cells (state : Native width Symbol Guard) : Prop where
  /-- The current physical machine is valid. -/
  machine : SourceRecursiveIntersectionKernel.Valid state.machine
  /-- Node cells retain physical inputs and returned availability. -/
  nodes : FlatMemoThunk.Valid (fun _ _ => True) (NodeGood state.machine) state.nodes
  /-- Edge cells retain physical inputs and returned residency. -/
  edges : FlatMemoThunk.Valid (fun _ _ => True) (EdgeGood state.machine) state.edges

/-- An actual valid machine admits empty physical memo tables. -/
private theorem initial_valid (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) : Cells (initial width machine) :=
  ⟨valid, FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Actual machine growth retains both checked memo families and their original inputs. -/
private theorem advance_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (after : Machine Symbol Guard) (checked : SourceRecursiveIntersectionKernel.Valid after)
    (growth : Extension state.machine after) : Cells (advance state after) :=
  ⟨checked, FlatMemoThunk.Valid.map _ _ _ _ valid.nodes (fun _ good => good.grows growth),
    FlatMemoThunk.Valid.map _ _ _ _ valid.edges (fun _ good => good.grows growth)⟩

/-- Node publication checks current original inputs and the source word range. -/
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

/-- Edge publication checks complete current rows and their original source word range. -/
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

/-- Completion stores an available value at its original running node handle. -/
private theorem finishNode_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.machine.heap value) :
    Cells (SourceRecursiveIntersectionThunks.finishNode handle value state) := by
  have good := valid.nodes.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle (.returned value) state.nodes _ _
    valid.nodes _ running ⟨good.1, available⟩, valid.edges⟩

/-- Completion stores a resident row at its original running edge handle. -/
private theorem finishEdge_valid
    (state : Native width Symbol Guard) (valid : Cells state)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (resident : EdgeResident state.machine.heap value) :
    Cells (SourceRecursiveIntersectionThunks.finishEdge handle value state) := by
  have good := valid.edges.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle (.returned value) state.edges _ _
    valid.edges _ running ⟨good.1, resident⟩⟩


/-- Initial native fields and resident cells suffice without semantic or word-range laws. -/
structure Good (state : Checked width) : Prop where
  /-- The two native cell families retain their physical records. -/
  native : Cells state.native
  /-- The constructor heap retains its semantic and depth invariants. -/
  heap : SourceEqualityRequiredCache.Ready state.native.machine.heap
  /-- Equality operation caches retain valid completed entries. -/
  operations : SourceEqualityConstraintMemoAllocation.Valid state.operations
  /-- Every stored edge guard has an available allocated field. -/
  fields : Fields state.operations state.native.machine.heap

/-- Stronger checked physical validity supplies the weaker range-free invariant. -/
theorem Good.of_checked {state : Checked width}
    (valid : SourceCurrentAllocatedNativePhysicalCompletion.Good state) : Good state := by
  refine ⟨⟨valid.native.machine, ?_, ?_⟩,valid.heap,valid.operations,valid.fields⟩
  · exact FlatMemoThunk.Valid.keyMap _ _ _ _ valid.native.nodes (fun _ _ _ => trivial)
  · exact FlatMemoThunk.Valid.keyMap _ _ _ _ valid.native.edges (fun _ _ _ => trivial)

private theorem replace_native {state : Checked width} (good : Good state)
    (native : Native width Symbol Guard) (valid : Cells native)
    (same : native.machine = state.native.machine) : Good ⟨native,state.operations⟩ :=
  ⟨valid,same.symm ▸ good.heap,good.operations,same.symm ▸ good.fields⟩

private theorem changed {state : Checked width} (good : Good state)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (growth : Extension state.native.machine machine)
    (keeps : SourceEqualityRequiredCache.Keeps state.native.machine.heap machine.heap)
    (fields : Fields state.operations machine.heap) :
    Good ⟨advance state.native machine,state.operations⟩ :=
  ⟨advance_valid state.native good.native machine valid growth,keeps.ready,good.operations,fields⟩

private theorem finish_node {state : Checked width} (good : Good state)
    (handle : Nat) (value : Value Symbol Guard) (available : Available state.native.machine.heap value) :
    Good ⟨finishNode handle value state.native,state.operations⟩ := by
  apply replace_native good (finishNode handle value state.native) ?_ rfl
  cases found : state.native.nodes.cells handle with
  | none => simpa only [finishNode,FlatMemoThunk.finish,found] using good.native
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | suspended | returned result => simpa only [finishNode,FlatMemoThunk.finish,found] using good.native
      | evaluating => exact finishNode_valid state.native good.native handle request value found available

private theorem finish_edge {state : Checked width} (good : Good state)
    (handle : Nat) (value : EdgeValue Symbol Guard) (available : EdgeResident state.native.machine.heap value) :
    Good ⟨finishEdge handle value state.native,state.operations⟩ := by
  apply replace_native good (finishEdge handle value state.native) ?_ rfl
  cases found : state.native.edges.cells handle with
  | none => simpa only [finishEdge,FlatMemoThunk.finish,found] using good.native
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | suspended | returned result => simpa only [finishEdge,FlatMemoThunk.finish,found] using good.native
      | evaluating => exact finishEdge_valid state.native good.native handle request value found available

private theorem step_after {control next : Control A} {state after : Checked width} {value : A}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (one : step control state = .yielded next after)
    (actual : Steps (fuel+1) control state (.code (.pure value)) final) :
    Steps fuel next after (.code (.pure value)) final := by
  cases actual with
  | cons _ _ rest middle _ _ _ observed tail =>
    obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (observed.symm.trans one)
    exact tail

private theorem effects_trans {before middle after : Checked width}
    (first : Extension before.native.machine middle.native.machine)
    (last : Extension middle.native.machine after.native.machine)
    (firstKeeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
    (lastKeeps : SourceEqualityRequiredCache.Keeps middle.native.machine.heap after.native.machine.heap) :
    Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap :=
  ⟨first.trans last,firstKeeps.trans lastKeeps⟩

private def CodeAt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (count : Nat) : Prop :=
  ∀ {A : Type} (code : Code Symbol Guard A) (state after : Checked width) (value : A)
    (post : Machine Symbol Guard → A → Prop),
    Steps count (.code code) state (.code (.pure value)) after → Good state →
    Safe code state.native.machine post → Operands code state.native.machine → CodeFields state.operations code →
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧ post after.native.machine value

private def BodyAt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (count : Nat) : Prop :=
  ∀ (request : EdgeRequest Symbol Guard) (state after : Checked width) (value : EdgeValue Symbol Guard),
    Steps count (.edgeBody request .pure) state (.code (.pure value)) after → Good state → EdgeReady state.native.machine request →
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧ EdgeResident after.native.machine.heap value

private theorem node_part [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) (ih : ∀ smaller, smaller < count+1 → CodeAt (width := width) smaller)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state after : Checked width) (value : A) (post : Machine Symbol Guard → A → Prop)
    (actual : Steps (count+1) (.code (.node request next)) state (.code (.pure value)) after)
    (good : Good state) (safe : Safe (.node request next) state.native.machine post)
    (operands : Operands (.node request next) state.native.machine)
    (fields : CodeFields state.operations (.node request next)) :
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧ post after.native.machine value := by
  have chosenGood := lookupNode_valid state.native good.native request safe.1
  cases selected : lookupNode width request state.native with
  | mk selection chosen =>
    simp only [selected] at chosenGood
    cases selection with
    | direct captured =>
      obtain ⟨same,retained⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request captured state.native chosen selected
      subst captured
      subst chosen
      have one : step (.code (.node request next)) state = .yielded (.code ((compileNode request).bind next)) state := by
        simp only [step,SourceRecursiveIntersectionNative.step,selected,lift]
      have tail := step_after one actual
      obtain ⟨inner,outer,result,middle,total,body,rest⟩ := steps_bind_inverse count (.code (compileNode request)) next state after value tail
      have built := ih inner (by omega) (compileNode request) state middle result _ body good
        (compileNode_safe request state.native.machine good.native.machine safe.1)
        (SourceCurrentAllocatedNativeCodeProgress.compileNode_operands request state.native.machine good.native.machine safe.1)
        (SourceCurrentAllocatedNativeCodeFields.compileNode_fields _ request)
      have grown := SourceCurrentOperationGrowth.native (inner+1) (.code (compileNode request)) state
      rw [trace_done _ _ _ _ _ body] at grown
      have laterFields := SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations middle.operations (next result) (fields result) grown
      have completed := ih outer (by omega) (next result) middle after value post rest built.1
        (safe.2 result middle.native.machine built.1.native.machine built.2.1 built.2.2.2)
        (operands.2 result middle.native.machine built.1.native.machine built.2.1 built.2.2.2) laterFields
      exact ⟨completed.1,built.2.1.trans completed.2.1,built.2.2.1.trans completed.2.2.1,completed.2.2.2⟩
    | memoized handle =>
      have chosenMachine : chosen.machine = state.native.machine := by
        simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request state.native
      have chosenState := replace_native good chosen chosenGood chosenMachine
      have currentGood := demandNode_valid chosen chosenGood handle
      cases demanded : demandNode handle chosen with
      | mk observation current =>
        simp only [demanded] at currentGood
        have currentMachine : current.machine = state.native.machine := by
          simpa only [demanded] using (SourceRecursiveIntersectionNative.demandNode_machine handle chosen).trans chosenMachine
        have currentState := replace_native good current currentGood currentMachine
        have startKeeps : SourceEqualityRequiredCache.Keeps state.native.machine.heap current.machine.heap := by
          rw [currentMachine]
          exact SourceEqualityRequiredCache.pure_keeps _ good.heap
        cases observation with
        | absent | busy =>
          have one := (steps_succ count _ _ _ _ actual).choose_spec.choose_spec.1
          simp only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] at one
          cases one
        | ready result =>
          have one : step (.code (.node request next)) state = .yielded (.code (next result)) ⟨current,state.operations⟩ := by
            simp only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift]
          have tail := step_after one actual
          obtain ⟨captured,present,same⟩ := SourceRecursiveIntersectionNative.demandNode_ready handle chosen current result demanded
          have available := (chosenGood.nodes.checked handle _ present).2
          have currentAvailable : Available current.machine.heap result := by rw [same]; exact available
          have startExtension : Extension state.native.machine current.machine := currentMachine.symm ▸ Extension.refl _
          have completed := ih count (by omega) (next result) ⟨current,state.operations⟩ after value post tail currentState
            (safe.2 result current.machine currentGood.machine startExtension currentAvailable)
            (operands.2 result current.machine currentGood.machine startExtension currentAvailable) (fields result)
          exact ⟨completed.1,startExtension.trans completed.2.1,
            startKeeps.trans completed.2.2.1,completed.2.2.2⟩
        | evaluate captured =>
          have one : step (.code (.node request next)) state =
              .yielded (.code ((compileNode captured).bind (fun result => .finishNode handle result (next result)))) ⟨current,state.operations⟩ := by
            simp only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift]
          have tail := step_after one actual
          have running := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen current captured demanded).2
          have capturedReady := (currentGood.nodes.checked handle _ running).1
          obtain ⟨inner,outer,result,middle,total,body,rest⟩ := steps_bind_inverse count (.code (compileNode captured))
            (fun result => .finishNode handle result (next result)) ⟨current,state.operations⟩ after value tail
          have built := ih inner (by omega) (compileNode captured) ⟨current,state.operations⟩ middle result _ body currentState
            (compileNode_safe captured current.machine currentGood.machine capturedReady)
            (SourceCurrentAllocatedNativeCodeProgress.compileNode_operands captured current.machine currentGood.machine capturedReady)
            (SourceCurrentAllocatedNativeCodeFields.compileNode_fields _ captured)
          have grown := SourceCurrentOperationGrowth.native (inner+1) (.code (compileNode captured)) ⟨current,state.operations⟩
          rw [trace_done _ _ _ _ _ body] at grown
          have finishedGood := finish_node built.1 handle result built.2.2.2
          cases rest with
          | cons _ _ resume reached _ _ suffix finish rest =>
            have observed : step (.code (.finishNode handle result (next result))) middle =
                .yielded (.code (next result)) ⟨finishNode handle result middle.native,middle.operations⟩ := rfl
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (finish.symm.trans observed)
            have startExtension : Extension state.native.machine current.machine := currentMachine.symm ▸ Extension.refl _
            have allGrowth := startExtension.trans built.2.1
            have completed := ih suffix (by omega) (next result) _ after value post rest finishedGood
              (safe.2 result middle.native.machine built.1.native.machine allGrowth built.2.2.2)
              (operands.2 result middle.native.machine built.1.native.machine allGrowth built.2.2.2)
              (SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations middle.operations (next result) (fields result) grown)
            exact ⟨completed.1,allGrowth.trans completed.2.1,
              (startKeeps.trans built.2.2.1).trans completed.2.2.1,
              completed.2.2.2⟩

private theorem body_part [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) (ih : ∀ smaller, smaller < count+1 → CodeAt (width := width) smaller) : BodyAt (width := width) (count+1) := by
  intro request state after value actual good ready
  obtain ⟨code,operations,one,valid,growth,retained,fields⟩ :=
    SourceCurrentAllocatedNativeFieldClosure.body_complete request .pure state good.operations good.fields ready (fun _ => trivial)
  have tail := step_after (control := .edgeBody request .pure) one actual
  have prefixGood : Good {state with operations := operations} := ⟨good.native,good.heap,valid,retained⟩
  have certified := SourceCurrentAllocatedNativeCodeProgress.body_certified request state {state with operations := operations}
    code good.native.machine ready one
  exact ih count (by omega) code {state with operations := operations} after value _ tail prefixGood certified.1 certified.2 fields

private theorem edge_part [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) (ih : ∀ smaller, smaller < count+1 → CodeAt (width := width) smaller)
    (bodyIH : ∀ smaller, smaller < count+1 → BodyAt (width := width) smaller)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state after : Checked width) (value : A) (post : Machine Symbol Guard → A → Prop)
    (actual : Steps (count+1) (.code (.edge request next)) state (.code (.pure value)) after)
    (good : Good state) (safe : Safe (.edge request next) state.native.machine post)
    (operands : Operands (.edge request next) state.native.machine)
    (fields : CodeFields state.operations (.edge request next)) :
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧ post after.native.machine value := by
  have chosenGood := lookupEdge_valid state.native good.native request safe.1
  cases selected : lookupEdge width request state.native with
  | mk handle chosen =>
    simp only [selected] at chosenGood
    have chosenMachine : chosen.machine = state.native.machine := by
      simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request state.native
    have currentGood := demandEdge_valid chosen chosenGood handle
    cases demanded : demandEdge handle chosen with
    | mk observation current =>
      simp only [demanded] at currentGood
      have currentMachine : current.machine = state.native.machine := by
        simpa only [demanded] using (SourceRecursiveIntersectionNative.demandEdge_machine handle chosen).trans chosenMachine
      have currentState := replace_native good current currentGood currentMachine
      have startKeeps : SourceEqualityRequiredCache.Keeps state.native.machine.heap current.machine.heap := by
        rw [currentMachine]
        exact SourceEqualityRequiredCache.pure_keeps _ good.heap
      have startExtension : Extension state.native.machine current.machine := currentMachine.symm ▸ Extension.refl _
      cases observation with
      | absent | busy =>
        have one := (steps_succ count _ _ _ _ actual).choose_spec.choose_spec.1
        simp only [step,selected,demanded] at one
        cases one
      | ready result =>
        have one : step (.code (.edge request next)) state = .yielded (.code (next result)) ⟨current,state.operations⟩ := by
          simp only [step,selected,demanded]
        have tail := step_after one actual
        obtain ⟨captured,present,same⟩ := SourceRecursiveIntersectionNative.demandEdge_ready handle chosen current result demanded
        have available := (chosenGood.edges.checked handle _ present).2
        have currentAvailable : EdgeResident current.machine.heap result := by rw [same]; exact available
        have completed := ih count (by omega) (next result) ⟨current,state.operations⟩ after value post tail currentState
          (safe.2 result current.machine currentGood.machine startExtension currentAvailable)
          (operands.2 result current.machine currentGood.machine startExtension currentAvailable) (fields result)
        exact ⟨completed.1,startExtension.trans completed.2.1,startKeeps.trans completed.2.2.1,completed.2.2.2⟩
      | evaluate captured =>
        have one : step (.code (.edge request next)) state =
            .yielded (.edgeBody captured (fun result => .finishEdge handle result (next result))) ⟨current,state.operations⟩ := by
          simp only [step,selected,demanded]
        have tail := step_after one actual
        have running := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen current captured demanded).2
        have capturedReady := (currentGood.edges.checked handle _ running).1
        obtain ⟨inner,outer,result,middle,total,body,rest⟩ := steps_bind_inverse count (.edgeBody captured .pure)
          (fun result => .finishEdge handle result (next result)) ⟨current,state.operations⟩ after value tail
        have built := bodyIH inner (by omega) captured ⟨current,state.operations⟩ middle result body currentState capturedReady
        have grown := SourceCurrentOperationGrowth.native (inner+1) (.edgeBody captured .pure) ⟨current,state.operations⟩
        rw [trace_done _ _ _ _ _ body] at grown
        have finishedGood := finish_edge built.1 handle result built.2.2.2
        cases rest with
        | cons _ _ resume reached _ _ suffix finish rest =>
          have observed : step (.code (.finishEdge handle result (next result))) middle =
              .yielded (.code (next result)) ⟨finishEdge handle result middle.native,middle.operations⟩ := rfl
          obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (finish.symm.trans observed)
          have allGrowth := startExtension.trans built.2.1
          have completed := ih suffix (by omega) (next result) _ after value post rest finishedGood
            (safe.2 result middle.native.machine built.1.native.machine allGrowth built.2.2.2)
            (operands.2 result middle.native.machine built.1.native.machine allGrowth built.2.2.2)
            (SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations middle.operations (next result) (fields result) grown)
          exact ⟨completed.1,allGrowth.trans completed.2.1,(startKeeps.trans built.2.2.1).trans completed.2.2.1,completed.2.2.2⟩

private theorem code_part [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) (ih : ∀ smaller, smaller < count+1 → CodeAt (width := width) smaller)
    (bodyIH : ∀ smaller, smaller < count+1 → BodyAt (width := width) smaller) : CodeAt (width := width) (count+1) := by
  intro A code state after value post actual good safe operands fields
  cases code with
  | pure original =>
    have impossible := (pure_trace (count+1) original value state after actual).1
    omega
  | fail failure =>
    obtain ⟨next,current,one,tail⟩ := steps_succ count _ _ _ _ actual
    cases one
  | node request next => exact node_part count ih request next state after value post actual good safe operands fields
  | edge request next => exact edge_part count ih bodyIH request next state after value post actual good safe operands fields
  | finishNode | finishEdge => cases safe
  | work job next =>
    let made := run job state.native.machine.heap
    let machine := {state.native.machine with heap := made.2}
    let middle : Checked width := ⟨advance state.native machine,state.operations⟩
    have one : step (.code (.work job next)) state = .yielded (.code (next made.1)) middle := rfl
    have tail := step_after one actual
    have done : SourceRecursiveIntersectionKernel.work job state.native.machine = .done made.1 machine := rfl
    have machineValid : SourceRecursiveIntersectionKernel.Valid machine := by
      simpa only [done,Result.state] using safe.1
    have growth : Extension state.native.machine machine := by simpa only [done,Result.state] using safe.2.1
    have kept := SourceEqualityNativeDemandHeapPrimitives.work_keeps job state.native.machine.heap good.heap operands.1
    have annotations := SourceCurrentAllocatedNativeCodeFields.work_heap state.operations job state.native.machine.heap good.fields fields.1
    have currentGood : Good middle := changed good machine machineValid growth kept annotations
    have completed := ih count (by omega) (next made.1) middle after value post tail currentGood
      (safe.2.2 made.1 machine done) (operands.2 made.1 machine done) (fields.2 made.1)
    exact ⟨completed.1,growth.trans completed.2.1,kept.trans completed.2.2.1,completed.2.2.2⟩
  | enter domain left right first second next =>
    let entered := SourceRecursiveIntersectionEnvironment.enter state.native.machine.domains domain.key left right first second
    let machine := {state.native.machine with domains := entered.2}
    let middle : Checked width := ⟨advance state.native machine,state.operations⟩
    have one : step (.code (.enter domain left right first second next)) state = .yielded (.code (next entered.1)) middle := rfl
    have tail := step_after one actual
    have kept : SourceEqualityRequiredCache.Keeps state.native.machine.heap machine.heap := SourceEqualityRequiredCache.pure_keeps _ good.heap
    have currentGood : Good middle := changed good machine safe.1 safe.2.1 kept good.fields
    have completed := ih count (by omega) (next entered.1) middle after value post tail currentGood
      safe.2.2 operands.2.2.2 (fields entered.1)
    exact ⟨completed.1,safe.2.1.trans completed.2.1,kept.trans completed.2.2.1,completed.2.2.2⟩
  | read name next =>
    have one : step (.code (.read name next)) state =
        .yielded (.code (next (SourcePreparedSharedRows.read state.native.machine.heap name))) state := rfl
    exact ih count (by omega) _ state after value post (step_after one actual) good safe operands (fields _)
  | optionalBinder pair input next =>
    have retained := SourceCurrentAllocatedNativeCodeFields.optionalBinder_heap state.operations pair input state.native.machine.heap
      good.native.machine.1 good.fields operands.1
    have kept := SourceEqualityNativeDemandHeapPrimitives.optionalBinder_keeps pair input state.native.machine.heap good.heap operands.1
    cases built : SourceRecursiveIntersectionMaybeMu.maybeMu pair input state.native.machine.heap with
    | pending key heap =>
      obtain ⟨next,current,one,tail⟩ := steps_succ count _ _ _ _ actual
      simp only [step,SourceRecursiveIntersectionNative.step,built,lift] at one
      cases one
    | done result heap =>
      let machine := {state.native.machine with heap := heap}
      let middle : Checked width := ⟨advance state.native machine,state.operations⟩
      have done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair input state.native.machine.heap) state.native.machine =
          .done result machine := by rw [built]; rfl
      have one : step (.code (.optionalBinder pair input next)) state = .yielded (.code (next result)) middle := by
        simp only [step,SourceRecursiveIntersectionNative.step,built,lift]
        rfl
      have tail := step_after one actual
      have machineValid : SourceRecursiveIntersectionKernel.Valid machine := by simpa only [done,Result.state] using safe.1
      have growth : Extension state.native.machine machine := by simpa only [done,Result.state] using safe.2.1
      have actualKeeps : SourceEqualityRequiredCache.Keeps state.native.machine.heap heap := by
        simpa only [built,InternedNestedConstruction.Outcome.state] using kept
      have annotations : Fields state.operations heap := by
        simpa only [built,InternedNestedConstruction.Outcome.state] using retained
      have currentGood : Good middle := changed good machine machineValid growth actualKeeps annotations
      have completed := ih count (by omega) (next result) middle after value post tail currentGood
        (safe.2.2 result machine done) (operands.2 result machine done) (fields result)
      exact ⟨completed.1,growth.trans completed.2.1,actualKeeps.trans completed.2.2.1,completed.2.2.2⟩

private theorem all_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (count : Nat) :
    CodeAt (width := width) count ∧ BodyAt (width := width) count := by
  induction count using Nat.strongRecOn with
  | ind count ih =>
    cases count with
    | zero =>
      constructor
      · intro A code state after value post actual good safe operands fields
        obtain ⟨same,retained⟩ := steps_zero _ _ _ _ actual
        cases same
        cases retained
        exact ⟨good,.refl _,SourceEqualityRequiredCache.pure_keeps _ good.heap,safe⟩
      · intro request state after value actual
        have impossible := (steps_zero _ _ _ _ actual).1
        cases impossible
    | succ count =>
      exact ⟨code_part count (fun smaller below => (ih smaller below).1) (fun smaller below => (ih smaller below).2),
        body_part count (fun smaller below => (ih smaller below).1)⟩

/-- An actual completed compiled call derives physical and equality invariants without reached checks. -/
theorem code [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (program : Code Symbol Guard A) (state after : Checked width) (value : A)
    (post : Machine Symbol Guard → A → Prop) (good : Good state)
    (safe : Safe program state.native.machine post) (operands : Operands program state.native.machine)
    (fields : CodeFields state.operations program)
    (actual : execute fuel (.code program) state = .done value after) :
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ post after.native.machine value := by
  obtain ⟨count,below,trace⟩ := done_trace fuel (.code program) state after value actual
  have checked := (all_done count).1 program state after value post trace good safe operands fields
  have growth := SourceCurrentOperationGrowth.native fuel (.code program) state
  rw [actual] at growth
  exact ⟨checked.1,checked.2.1,checked.2.2.1,growth,checked.2.2.2⟩

/-- Empty native result tables derive the invariant from initial physical and allocated-field facts. -/
theorem initial (machine : Machine Symbol Guard) (operations : Operations)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (ready : SourceEqualityRequiredCache.Ready machine.heap)
    (operationValid : SourceEqualityConstraintMemoAllocation.Valid operations) (fields : Fields operations machine.heap) :
    Good ⟨SourceRecursiveIntersectionThunks.initial width machine,operations⟩ :=
  ⟨initial_valid machine valid,ready,operationValid,fields⟩

/-- A literal completed node request derives operation validity from its initial available operands. -/
theorem node [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (state after : Checked width) (value : Value Symbol Guard)
    (good : Good state) (ready : NodeReady state.native.machine request)
    (actual : execute fuel (.code (requestNode request.domain request.left request.right)) state = .done value after) :
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ Available after.native.machine.heap value :=
  code fuel (requestNode request.domain request.left request.right) state after value _ good
    (safe_requestNode request.domain request.left request.right state.native.machine ready)
    ⟨ready,fun _ _ _ _ _ => trivial⟩ (fun _ => trivial) actual

/-- A literal completed row request derives valid caches and its actual resident returned row. -/
theorem edge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : EdgeRequest Symbol Guard) (state after : Checked width) (value : EdgeValue Symbol Guard)
    (good : Good state) (ready : EdgeReady state.native.machine request)
    (actual : execute fuel (.code (requestEdge request.domain request.left request.right)) state = .done value after) :
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ EdgeResident after.native.machine.heap value :=
  code fuel (requestEdge request.domain request.left request.right) state after value _ good
    (safe_requestEdge request.domain request.left request.right state.native.machine ready)
    ⟨ready,fun _ _ _ _ _ => trivial⟩ (fun _ => trivial) actual

/-- Actual node completion followed by indexed descent derives the new inherited value's readiness. -/
theorem node_dispatch [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (state after : Checked width) (value : Value Symbol Guard)
    (combined : SourceEqualityConstraintAllocation.Value) (index : Nat)
    (good : Good state) (ready : NodeReady state.native.machine request)
    (inherited : SourceEqualityConstraintAllocation.Ready state.operations.constraints combined)
    (actual : execute fuel (.code (requestNode request.domain request.left request.right)) state = .done value after) :
    let result := SourceEqualityConstraintMemoAllocation.descend combined index after.operations
    Good {after with operations := result.2} ∧
      SourceEqualityConstraintAllocation.Ready result.2.constraints result.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations result.2 := by
  obtain ⟨final,extension,keeps,growth,available⟩ := node fuel request state after value good ready actual
  have descended := SourceEqualityConstraintMemoAllocation.descend_correct combined index after.operations final.operations
    (inherited.grows growth.constraint_growth)
  exact ⟨⟨final.native,final.heap,descended.1,final.fields.grows descended.2.2.2⟩,
    descended.2.1,SourceCurrentConjunctionEquality.grows_trans growth descended.2.2.2⟩

end MicroCFTA.SourceCurrentNativeOperationInvariants
