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
      obtain ⟨rfl,rfl⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request captured state.native chosen selected
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
            (currentMachine.symm ▸ SourceEqualityRequiredCache.pure_keeps _ good.heap).trans completed.2.2.1,completed.2.2.2⟩
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
          | refl => contradiction
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
              ((currentMachine.symm ▸ SourceEqualityRequiredCache.pure_keeps _ good.heap).trans built.2.2.1).trans completed.2.2.1,
              completed.2.2.2⟩

end MicroCFTA.SourceCurrentNativeOperationInvariants
