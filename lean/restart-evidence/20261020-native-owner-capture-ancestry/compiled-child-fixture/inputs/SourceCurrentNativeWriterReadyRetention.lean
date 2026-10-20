import MicroCFTA.SourceCurrentNativeNodeWriterHistory
import MicroCFTA.SourceEqualityNativeDemandMemo

/-!
# Ready edge cells at captured node-body returns

Actual checked steps retain returned cells in both native families.
The existing causal history therefore retains those exact cells from an
earlier captured node-body return to the current reader. Final edge-writer
history can describe them without History at an internal active owner.
-/
namespace MicroCFTA.SourceCurrentNativeWriterReadyRetention
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects fields_before_bind)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}

/-- Each actual checked trace retains all earlier returned cells and published handles. -/
theorem trace_retained [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {A : Type} {fuel : Nat} {control next : Control A} {before after : Checked width}
    (actual : Trace fuel control before next after) (shape : SourceRecursiveIntersectionNative.Shape before.native) :
    Retained before.native after.native := by
  induction actual with
  | refl => exact Retained.refl _
  | cons control before next middle final after fuel inputs one rest ih =>
    have first := SourceEqualityNativeDemandMemo.step_preserves control before shape
    simp only [one,Outcome.state] at first
    exact first.2.trans (ih first.1)

/-- A returned node retains its exact captured owner, compiled result, finish, and writer-to-reader growth. -/
def Written [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (reader : Native width Symbol Guard) : Prop :=
  ∃ (before after : Checked width) (fuel : Nat),
    Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
      {after with native := finishNode handle result after.native} ∧
    Grows before.native.machine.heap reader.machine.heap ∧ Grows after.native.machine.heap reader.machine.heap ∧
      Retained after.native reader

/-- The stronger receipt retains the earlier exact node writer and both heap growth facts. -/
theorem Written.forget [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {handle : Nat} {request : NodeRequest Symbol Guard} {result : Value Symbol Guard} {reader : Native width Symbol Guard}
    (written : Written (width := width) handle request result reader) :
    SourceCurrentNativeNodeWriterHistory.Written (width := width) handle request result reader.machine.heap := by
  obtain ⟨before,after,fuel,good,ready,owner,body,retained,finished,first,last,cells⟩ := written
  exact ⟨before,after,fuel,good,ready,owner,body,retained,finished,first,last⟩

private theorem later [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {handle : Nat} {request : NodeRequest Symbol Guard} {result : Value Symbol Guard}
    {reader next : Native width Symbol Guard}
    (written : Written (width := width) handle request result reader)
    (growth : Grows reader.machine.heap next.machine.heap) (cells : Retained reader next) :
    Written (width := width) handle request result next := by
  obtain ⟨before,after,fuel,good,ready,owner,body,retained,finished,first,last,earlier⟩ := written
  exact ⟨before,after,fuel,good,ready,owner,body,retained,finished,
    grows_trans first growth,grows_trans last growth,earlier.trans cells⟩

private theorem edge_nodes (request : EdgeRequest Symbol Guard) (state : Native width Symbol Guard) :
    (lookupEdge width request state).2.nodes = state.nodes := rfl

private theorem demand_edge_nodes (handle : Nat) (state : Native width Symbol Guard) :
    (demandEdge handle state).2.nodes = state.nodes := rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def Recorded (state : Native width Symbol Guard) : Prop :=
  ∀ handle request result, state.nodes.cells handle = some ⟨request,.returned result⟩ →
    Written (width := width) handle request result state

private theorem recorded_change (before after : Native width Symbol Guard) (known : Recorded before)
    (same : after.nodes = before.nodes) (growth : Grows before.machine.heap after.machine.heap)
    (cells : Retained before after) : Recorded after := by
  intro handle request result stored
  exact later (known handle request result (same ▸ stored)) growth cells

private theorem recorded_lookup (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (shape : SourceRecursiveIntersectionNative.Shape state) (known : Recorded state) :
    Recorded (lookupNode width request state).2 := by
  have cells := SourceEqualityNativeDemandMemo.lookupNode_retained request state shape
  have sameHeap : Grows state.machine.heap (lookupNode width request state).2.machine.heap := by
    rw [SourceRecursiveIntersectionNative.lookupNode_machine]
    exact grows_refl _
  cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode,requested] using known
  | some key =>
    cases found : state.nodes.table key with
    | some handle => simpa only [lookupNode,requested,FlatMemoThunk.lookupOrInsert,found] using known
    | none =>
      intro handle original result stored
      by_cases same : handle = state.nodes.next
      · subst handle
        simp [lookupNode,requested,FlatMemoThunk.lookupOrInsert,found,Cache.put] at stored
      · have originalStored : state.nodes.cells handle = some ⟨original,.returned result⟩ := by
          simpa only [lookupNode,requested,FlatMemoThunk.lookupOrInsert,found,Cache.put,ite_eq_right same] using stored
        exact later (known handle original result originalStored) sameHeap cells

private theorem recorded_demand (state : Native width Symbol Guard) (handle : Nat)
    (known : Recorded state) : Recorded (demandNode handle state).2 := by
  have cells := SourceEqualityNativeDemandMemo.demandNode_retained handle state
  have sameHeap : Grows state.machine.heap (demandNode handle state).2.machine.heap := by
    rw [SourceRecursiveIntersectionNative.demandNode_machine]
    exact grows_refl _
  cases found : state.nodes.cells handle with
  | none => simpa only [demandNode,FlatMemoThunk.demand,found] using known
  | some cell =>
    cases cell with
    | mk request phase =>
      cases phase with
      | evaluating | returned value => simpa only [demandNode,FlatMemoThunk.demand,found] using known
      | suspended =>
        intro other original value stored
        by_cases same : other = handle
        · subst other
          simp [demandNode,FlatMemoThunk.demand,found,FlatMemoThunk.setStatus,Cache.put] at stored
        · have originalStored : state.nodes.cells other = some ⟨original,.returned value⟩ := by
            simpa only [demandNode,FlatMemoThunk.demand,found,FlatMemoThunk.setStatus,Cache.put,ite_eq_right same] using stored
          exact later (known other original value originalStored) sameHeap cells

private theorem recorded_finish (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (known : Recorded state) (owner : state.nodes.cells handle = some ⟨request,.evaluating⟩)
    (writer : Written (width := width) handle request result state) :
    Recorded (finishNode handle result state) := by
  have cells := SourceEqualityNativeDemandMemo.finishNode_retained handle result state
  intro other original value stored
  by_cases same : other = handle
  · subst other
    have equal : request = original ∧ result = value := by
      simpa [finishNode,FlatMemoThunk.finish,owner,FlatMemoThunk.setStatus,Cache.put] using stored
    rcases equal with ⟨rfl,rfl⟩
    exact later writer (grows_refl _) cells
  · have earlier : state.nodes.cells other = some ⟨original,.returned value⟩ := by
      simpa only [finishNode,FlatMemoThunk.finish,owner,FlatMemoThunk.setStatus,Cache.put,ite_eq_right same] using stored
    exact later (known other original value earlier) (grows_refl _) cells

private theorem yielded {A : Type} {control rest : Control A} {before after : Checked width}
    (good : Good before) (fields : Fields control before)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (one : step control before = .yielded rest after) :
    Good after ∧ Fields rest after ∧ Grows before.native.machine.heap after.native.machine.heap := by
  have actual := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good inputs fields
  exact ⟨by simpa only [one, Outcome.state] using actual.1,
    by simpa only [one, SourceCurrentAllocatedNativeFieldClosure.OutcomeFields] using actual.2.2.2.2.2,
    by simpa only [one, Outcome.state] using actual.2.2.1.growth⟩

private def Preserves (fuel : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before after : Checked width) (value : A),
    Clean control → Good before → Fields control before → Recorded before.native →
    Trace fuel control before (.code (.pure value)) after → Recorded after.native

private theorem preserves (fuel : Nat) : Preserves (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind count ih =>
    intro A control before after value clean good fields known trace
    cases trace with
    | refl => exact known
    | cons _ _ resume middle _ _ rest inputs one tail =>
      have next := yielded good fields inputs one
      have nextCells : Retained before.native middle.native := by
        have kept := (SourceEqualityNativeDemandMemo.step_preserves control before good.native.shape).2
        simpa only [one,Outcome.state] using kept
      cases control with
      | edgeBody request continuation =>
          change body request continuation before = .yielded resume middle at one
          have same : middle.native = before.native := by
            simpa only [one, Outcome.state] using SourceEqualityNativeDemandOperations.body_native request continuation before
          have nextClean := SourceEqualityNativeDemandBodyCode.body_clean request continuation before middle resume one clean
          exact ih rest (by omega) resume middle after value nextClean next.1 next.2.1 (same ▸ known) tail
      | code code =>
        cases code with
        | pure | fail => cases one
        | finishNode | finishEdge => cases clean
        | work job continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (run job before.native.machine.heap).1)) _ after value (clean _) next.1 next.2.1
              (recorded_change _ _ known rfl next.2.2 nextCells) tail
        | enter domain left right first second continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second).1)) _ after value (clean _) next.1 next.2.1 (recorded_change _ _ known rfl next.2.2 nextCells) tail
        | read name continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (SourcePreparedSharedRows.read before.native.machine.heap name))) _ after value (clean _) next.1 next.2.1 (recorded_change _ _ known rfl next.2.2 nextCells) tail
        | optionalBinder pair body continuation =>
            cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
            | pending key heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                cases one
            | done result heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
                exact ih rest (by omega) (.code (continuation result)) _ after value (clean _) next.1 next.2.1
                  (recorded_change _ _ known rfl next.2.2 nextCells) tail
        | node request continuation =>
            cases selected : lookupNode width request before.native with
            | mk selection chosen =>
              cases selection with
              | direct actual =>
                have chosenKnown := recorded_lookup before.native request good.native.shape known
                simp only [selected] at chosenKnown
                have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,lift] using one)
                rcases same with ⟨rfl,rfl⟩
                exact ih rest (by omega) (.code ((compileNode actual).bind continuation)) _ after value
                  (bodyCode_bind _ _ (compileNode_bodyCode actual) clean) next.1 next.2.1 chosenKnown tail
              | memoized handle =>
                have chosenKnown := recorded_lookup before.native request good.native.shape known
                simp only [selected] at chosenKnown
                cases demanded : demandNode handle chosen with
                | mk observation running =>
                  have runningKnown := recorded_demand chosen handle chosenKnown
                  simp only [demanded] at runningKnown
                  cases observation with
                  | absent | busy => simp only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] at one; cases one
                  | ready result =>
                      have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] using one)
                      rcases same with ⟨rfl,rfl⟩
                      exact ih rest (by omega) (.code (continuation result)) _ after value (clean result) next.1 next.2.1 runningKnown tail
                  | evaluate actual =>
                      have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] using one)
                      rcases same with ⟨rfl,rfl⟩
                      obtain ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest
                        (.code (compileNode actual)) (fun result => .finishNode handle result (continuation result))
                        ⟨running,before.operations⟩ after value tail
                      have bodyFields := fields_before_bind (.code (compileNode actual))
                        (fun result => .finishNode handle result (continuation result)) _ next.2.1
                      have bodyKnown := ih inner (by omega) (.code (compileNode actual)) _ current result (compileNode_bodyCode actual)
                        next.1 bodyFields runningKnown bodyTrace
                      have owner := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).2
                      have ownerKept := SourceEqualityNativeDemandProtectedPrefix.node_body_owner inner handle actual
                        ⟨running,before.operations⟩ current result next.1.native.shape owner bodyTrace.steps
                      have finishFacts := effects (bodyTrace.bind (fun result => .finishNode handle result (continuation result))) next.1 next.2.1
                      cases frameTrace with
                      | cons _ _ chosen reached _ _ count frameInputs frameStep remaining =>
                          obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                          have writer : Written (width := width) handle actual result current.native :=
                            ⟨⟨running,before.operations⟩,current,inner,next.1,(next.1.native.nodes.checked handle ⟨actual,.evaluating⟩ owner).1,owner,bodyTrace,ownerKept.1,
                              .cons _ _ _ _ _ _ _ frameInputs rfl (.refl _ _),
                              (effects bodyTrace next.1 bodyFields).2.2.1.growth,grows_refl _,Retained.refl _⟩
                          have finished := yielded finishFacts.1 finishFacts.2.2.2.2 frameInputs frameStep
                          have finishedKnown := recorded_finish current.native handle actual result bodyKnown ownerKept.1 writer
                          exact ih count (by omega) (.code (continuation result)) _ after value (clean result) finished.1 finished.2.1 finishedKnown remaining
        | edge request continuation =>
            cases selected : lookupEdge width request before.native with
            | mk handle chosen =>
              have chosenNodes : chosen.nodes = before.native.nodes := by
                simpa only [selected] using edge_nodes request before.native
              have chosenMachine : chosen.machine = before.native.machine := by
                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
              have chosenKnown : Recorded chosen := by
                intro handle original result stored
                exact later (known handle original result (chosenNodes ▸ stored)) (by rw [chosenMachine]; exact grows_refl _)
                  (by simpa only [selected] using SourceEqualityNativeDemandMemo.lookupEdge_retained request before.native good.native.shape)
              cases demanded : demandEdge handle chosen with
              | mk observation running =>
                have runningNodes : running.nodes = chosen.nodes := by
                  simpa only [demanded] using demand_edge_nodes handle chosen
                have runningMachine : running.machine = chosen.machine := by
                  simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
                have runningCells : Retained chosen running := by
                  simpa only [demanded] using SourceEqualityNativeDemandMemo.demandEdge_retained handle chosen
                have runningKnown : Recorded running := by
                  intro handle original result stored
                  exact later (chosenKnown handle original result (runningNodes ▸ stored)) (by rw [runningMachine]; exact grows_refl _)
                    runningCells
                cases observation with
                | absent | busy =>
                    simp only [step,selected,demanded] at one
                    cases one
                | ready result =>
                    have same := Outcome.yielded.inj (by simpa only [step,selected,demanded] using one)
                    rcases same with ⟨rfl,rfl⟩
                    exact ih rest (by omega) (.code (continuation result)) _ after value (clean result) next.1 next.2.1 runningKnown tail
                | evaluate actual =>
                    have same := Outcome.yielded.inj (by simpa only [step,selected,demanded] using one)
                    rcases same with ⟨rfl,rfl⟩
                    obtain ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest
                      (.edgeBody actual .pure) (fun result => .finishEdge handle result (continuation result))
                      ⟨running,before.operations⟩ after value tail
                    have bodyFields := fields_before_bind (.edgeBody actual .pure)
                      (fun result => .finishEdge handle result (continuation result)) _ next.2.1
                    have bodyKnown := ih inner (by omega) (.edgeBody actual .pure) _ current result (by intro value; trivial)
                      next.1 bodyFields runningKnown bodyTrace
                    have finishFacts := effects (bodyTrace.bind (fun result => .finishEdge handle result (continuation result))) next.1 next.2.1
                    cases frameTrace with
                    | cons _ _ chosen reached _ _ count frameInputs frameStep remaining =>
                        obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                        have finished := yielded finishFacts.1 finishFacts.2.2.2.2 frameInputs frameStep
                        exact ih count (by omega) (.code (continuation result)) _ after value (clean result) finished.1 finished.2.1
                          (recorded_change _ _ bodyKnown rfl (grows_refl _)
                            (SourceEqualityNativeDemandMemo.finishEdge_retained handle result current.native)) remaining

/-- The existing actual causal history derives an earlier node writer for every current returned cell. -/
theorem writers {state : Checked width} (history : History state) :
    ∀ handle request result, state.native.nodes.cells handle = some ⟨request,.returned result⟩ →
      Written (width := width) handle request result state.native := by
  induction history with
  | initial machine operations => intro handle request result impossible; cases impossible
  | advance earlier after growth ih => exact recorded_change _ _ ih rfl growth (SourceEqualityNativeDemandMemo.advance_retained _ _)
  | trace earlier control fuel value clean good fields actual ih =>
    exact preserves fuel control _ _ value clean good fields ih actual

/-- A captured body's ready edge cells use the final reader's actual earlier edge writers. -/
theorem edge_writers {state : Checked width} (history : History state)
    {handle : Nat} {request : NodeRequest Symbol Guard} {result : Value Symbol Guard}
    (written : Written (width := width) handle request result state.native) :
    ∃ (before after : Checked width) (fuel : Nat),
      Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Grows before.native.machine.heap state.native.machine.heap ∧
      Grows after.native.machine.heap state.native.machine.heap ∧
      ∀ edgeHandle original row, after.native.edges.cells edgeHandle = some ⟨original,.returned row⟩ →
        SourceCurrentNativeEdgeWriterGrowth.Written (width := width) edgeHandle original row state.native.machine.heap := by
  obtain ⟨before,after,fuel,good,ready,owner,body,retained,finished,first,last,cells⟩ := written
  exact ⟨before,after,fuel,good,ready,owner,body,retained,first,last,
    fun edgeHandle original row present => history.writers edgeHandle original row (cells.edges edgeHandle original row present)⟩

end MicroCFTA.SourceCurrentNativeWriterReadyRetention
