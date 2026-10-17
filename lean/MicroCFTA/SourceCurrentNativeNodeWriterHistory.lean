import MicroCFTA.SourceCurrentNativeEdgeWriterGrowth

/-!
# Actual same-handle native node writers

The existing causal history starts with empty native tables. Its completed
checked traces determine each returned node cell's earlier compiled body
and protected finish. Physical advances retain the full cell function and
record actual heap growth. A Mu result remains the literal whole value
returned by its compiled body. No reconstruction equality is assumed.
-/
namespace MicroCFTA.SourceCurrentNativeNodeWriterHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects fields_before_bind)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat}

/-- A returned node retains its exact captured owner, compiled result, finish, and writer-to-reader growth. -/
def Written [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (reader : Heap) : Prop :=
  ∃ (before after : Checked width) (fuel : Nat),
    Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
      {after with native := finishNode handle result after.native} ∧
    Grows before.native.machine.heap reader ∧ Grows after.native.machine.heap reader

/-- Later physical growth retains the same captured node writer and exact result. -/
theorem Written.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {handle : Nat} {request : NodeRequest Symbol Guard} {result : Value Symbol Guard} {reader later : Heap}
    (written : Written (width := width) handle request result reader) (growth : Grows reader later) :
    Written (width := width) handle request result later := by
  obtain ⟨before,after,fuel,good,ready,owner,body,retained,finished,first,last⟩ := written
  exact ⟨before,after,fuel,good,ready,owner,body,retained,finished,
    grows_trans first growth,grows_trans last growth⟩

private theorem edge_nodes (request : EdgeRequest Symbol Guard) (state : Native width Symbol Guard) :
    (lookupEdge width request state).2.nodes = state.nodes := rfl

private theorem demand_edge_nodes (handle : Nat) (state : Native width Symbol Guard) :
    (demandEdge handle state).2.nodes = state.nodes := rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def Recorded (state : Native width Symbol Guard) : Prop :=
  ∀ handle request result, state.nodes.cells handle = some ⟨request,.returned result⟩ →
    Written (width := width) handle request result state.machine.heap

private theorem recorded_change (before after : Native width Symbol Guard) (known : Recorded before)
    (same : after.nodes = before.nodes) (growth : Grows before.machine.heap after.machine.heap) :
    Recorded after := by
  intro handle request result stored
  exact (known handle request result (same ▸ stored)).grows growth

private theorem recorded_lookup (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (known : Recorded state) : Recorded (lookupNode width request state).2 := by
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
        simpa only [SourceRecursiveIntersectionNative.lookupNode_machine] using known handle original result originalStored

private theorem recorded_evaluating (state : Native width Symbol Guard) (handle : Nat)
    (known : Recorded state) :
    Recorded {state with nodes := FlatMemoThunk.setStatus handle .evaluating state.nodes} := by
  cases found : state.nodes.cells handle with
  | none => simpa only [FlatMemoThunk.setStatus, found] using known
  | some cell =>
      intro other request result stored
      by_cases same : other = handle
      · subst other
        simp [FlatMemoThunk.setStatus, found, Cache.put] at stored
      · exact known other request result (by
          simpa only [FlatMemoThunk.setStatus, found, Cache.put, ite_eq_right same] using stored)

private theorem recorded_demand (state : Native width Symbol Guard) (handle : Nat)
    (known : Recorded state) : Recorded (demandNode handle state).2 := by
  cases found : state.nodes.cells handle with
  | none => simpa only [demandNode, FlatMemoThunk.demand, found] using known
  | some cell =>
      cases cell with
      | mk request phase =>
          cases phase with
          | suspended => simpa only [demandNode, FlatMemoThunk.demand, found] using recorded_evaluating state handle known
          | evaluating | returned value => simpa only [demandNode, FlatMemoThunk.demand, found] using known

private theorem recorded_finish (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (known : Recorded state) (owner : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (writer : Written (width := width) handle request result state.machine.heap) :
    Recorded (SourceRecursiveIntersectionThunks.finishNode handle result state) := by
  intro other original value stored
  by_cases same : other = handle
  · subst other
    have equal : request = original ∧ result = value := by
      simpa [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, owner, FlatMemoThunk.setStatus, Cache.put] using stored
    rcases equal with ⟨rfl,rfl⟩
    exact writer
  · exact known other original value (by
      simpa only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, owner, FlatMemoThunk.setStatus,
        Cache.put, ite_eq_right same] using stored)

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
              (recorded_change _ _ known rfl next.2.2) tail
        | enter domain left right first second continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second).1)) _ after value (clean _) next.1 next.2.1 known tail
        | read name continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (SourcePreparedSharedRows.read before.native.machine.heap name))) _ after value (clean _) next.1 next.2.1 known tail
        | optionalBinder pair body continuation =>
            cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
            | pending key heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                cases one
            | done result heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
                exact ih rest (by omega) (.code (continuation result)) _ after value (clean _) next.1 next.2.1
                  (recorded_change _ _ known rfl next.2.2) tail
        | node request continuation =>
            cases selected : lookupNode width request before.native with
            | mk selection chosen =>
              cases selection with
              | direct actual =>
                have chosenKnown := recorded_lookup before.native request known
                simp only [selected] at chosenKnown
                have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,lift] using one)
                rcases same with ⟨rfl,rfl⟩
                exact ih rest (by omega) (.code ((compileNode actual).bind continuation)) _ after value
                  (bodyCode_bind _ _ (compileNode_bodyCode actual) clean) next.1 next.2.1 chosenKnown tail
              | memoized handle =>
                have chosenKnown := recorded_lookup before.native request known
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
                          have writer : Written (width := width) handle actual result current.native.machine.heap :=
                            ⟨⟨running,before.operations⟩,current,inner,next.1,(next.1.native.nodes.checked handle ⟨actual,.evaluating⟩ owner).1,owner,bodyTrace,ownerKept.1,
                              .cons _ _ _ _ _ _ _ frameInputs rfl (.refl _ _),
                              (effects bodyTrace next.1 bodyFields).2.2.1.growth,grows_refl _⟩
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
                rw [chosenMachine]
                exact known handle original result (chosenNodes ▸ stored)
              cases demanded : demandEdge handle chosen with
              | mk observation running =>
                have runningNodes : running.nodes = chosen.nodes := by
                  simpa only [demanded] using demand_edge_nodes handle chosen
                have runningMachine : running.machine = chosen.machine := by
                  simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
                have runningKnown : Recorded running := by
                  intro handle original result stored
                  rw [runningMachine]
                  exact chosenKnown handle original result (runningNodes ▸ stored)
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
                        exact ih count (by omega) (.code (continuation result)) _ after value (clean result) finished.1 finished.2.1 bodyKnown remaining

/-- The existing actual causal history derives an earlier node writer for every current returned cell. -/
theorem writers {state : Checked width} (history : History state) :
    ∀ handle request result, state.native.nodes.cells handle = some ⟨request,.returned result⟩ →
      Written (width := width) handle request result state.native.machine.heap := by
  induction history with
  | initial machine operations => intro handle request result impossible; cases impossible
  | advance earlier after growth ih => exact recorded_change _ _ ih rfl growth
  | trace earlier control fuel value clean good fields actual ih =>
    exact preserves fuel control _ _ value clean good fields ih actual

/-- A ready node demand identifies its complete captured request and its actual earlier protected writer. -/
theorem warm {state : Checked width} (history : History state) (good : Good state)
    (request : NodeRequest Symbol Guard) (chosen running : Native width Symbol Guard) (handle : Nat)
    (result : Value Symbol Guard) (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request state.native = (.memoized handle,chosen))
    (demanded : demandNode handle chosen = (.ready result,running)) :
    Written (width := width) handle request result state.native.machine.heap := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready request state.native chosen running handle result
    good.native ready safe selected demanded
  have known := recorded_lookup state.native request (writers history)
  simp only [selected] at known
  have machine : chosen.machine = state.native.machine := by
    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request state.native
  have written := known handle request result receipt.1
  rw [machine] at written
  exact written

end MicroCFTA.SourceCurrentNativeNodeWriterHistory
