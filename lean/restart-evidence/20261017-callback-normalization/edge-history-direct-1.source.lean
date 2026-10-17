import MicroCFTA.SourceCurrentNativeRowOrigins
import MicroCFTA.SourceEqualityNativeDemandBodyYield
import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix

/-!
# Earlier checked bodies of returned native edge cells

Clean source code has no explicit finish instruction. Actual cold calls
supply the protected body and finish traces before publication. Empty
native tables need no historical result premise.
-/
namespace MicroCFTA.SourceCurrentNativeEdgeHistory
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects fields_before_bind)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat}

/-- A literal earlier body retains its evaluating owner and its one actual finish. -/
def Writer (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) : Prop :=
  ∃ (handle : Nat) (before after : Checked width) (fuel : Nat),
    Good before ∧ EdgeReady before.native.machine request ∧
    before.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
    Trace fuel (.edgeBody request .pure) before (.code (.pure result)) after ∧
    after.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
    Trace 1 (.code (.finishEdge handle result (.pure result))) after (.code (.pure result))
      {after with native := SourceRecursiveIntersectionThunks.finishEdge handle result after.native}

private def Recorded (state : Native width Symbol Guard) : Prop :=
  ∀ handle request result, state.edges.cells handle = some ⟨request, .returned result⟩ → Writer (width := width) request result

private theorem recorded_lookup (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (known : Recorded state) : Recorded (lookupEdge width request state).2 := by
  cases found : state.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) with
  | some handle => simpa only [lookupEdge, FlatMemoThunk.lookupOrInsert, found] using known
  | none =>
      intro handle original result stored
      by_cases same : handle = state.edges.next
      · subst handle
        simp [lookupEdge, FlatMemoThunk.lookupOrInsert, found, Cache.put] at stored
      · exact known handle original result (by
          simpa only [lookupEdge, FlatMemoThunk.lookupOrInsert, found, Cache.put, ite_eq_right same] using stored)

private theorem recorded_evaluating (state : Native width Symbol Guard) (handle : Nat)
    (known : Recorded state) :
    Recorded {state with edges := FlatMemoThunk.setStatus handle .evaluating state.edges} := by
  cases found : state.edges.cells handle with
  | none => simpa only [FlatMemoThunk.setStatus, found] using known
  | some cell =>
      intro other request result stored
      by_cases same : other = handle
      · subst other
        simp [FlatMemoThunk.setStatus, found, Cache.put] at stored
      · exact known other request result (by
          simpa only [FlatMemoThunk.setStatus, found, Cache.put, ite_eq_right same] using stored)

private theorem recorded_demand (state : Native width Symbol Guard) (handle : Nat)
    (known : Recorded state) : Recorded (demandEdge handle state).2 := by
  cases found : state.edges.cells handle with
  | none => simpa only [demandEdge, FlatMemoThunk.demand, found] using known
  | some cell =>
      cases cell with
      | mk request phase =>
          cases phase with
          | suspended => simpa only [demandEdge, FlatMemoThunk.demand, found] using recorded_evaluating state handle known
          | evaluating | returned value => simpa only [demandEdge, FlatMemoThunk.demand, found] using known

private theorem recorded_finish (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (known : Recorded state) (owner : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (writer : Writer (width := width) request result) :
    Recorded (SourceRecursiveIntersectionThunks.finishEdge handle result state) := by
  intro other original value stored
  by_cases same : other = handle
  · subst other
    have equal : request = original ∧ result = value := by
      simpa [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, owner, FlatMemoThunk.setStatus, Cache.put] using stored
    rcases equal with ⟨rfl,rfl⟩
    exact writer
  · exact known other original value (by
      simpa only [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, owner, FlatMemoThunk.setStatus,
        Cache.put, ite_eq_right same] using stored)

private theorem yielded {A : Type} {control rest : Control A} {before after : Checked width}
    (good : Good before) (fields : Fields control before)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (one : step control before = .yielded rest after) : Good after ∧ Fields rest after := by
  have actual := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good inputs fields
  exact ⟨by simpa only [one, Outcome.state] using actual.1,
    by simpa only [one, SourceCurrentAllocatedNativeFieldClosure.OutcomeFields] using actual.2.2.2.2.2⟩

private theorem node_edges (request : NodeRequest Symbol Guard) (state : Native width Symbol Guard) :
    (lookupNode width request state).2.edges = state.edges := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right <;>
    simp only [lookupNode,key]

private theorem demand_node_edges (handle : Nat) (state : Native width Symbol Guard) :
    (demandNode handle state).2.edges = state.edges := rfl

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
          have same : middle.native = before.native := by
            simpa only [one, Outcome.state] using SourceEqualityNativeDemandOperations.body_native request continuation before
          have nextClean := SourceEqualityNativeDemandBodyCode.body_clean request continuation before middle resume one clean
          exact ih rest (by omega) resume middle after value nextClean next.1 next.2 (same ▸ known) tail
      | code code =>
        cases code with
        | pure | fail => cases one
        | finishNode | finishEdge => cases clean
        | work job continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) _ _ after value (clean _) next.1 next.2 known tail
        | enter domain left right first second continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) _ _ after value (clean _) next.1 next.2 known tail
        | read name continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) _ _ after value (clean _) next.1 next.2 known tail
        | optionalBinder pair body continuation =>
            cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
            | pending key heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                cases one
            | done result heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
                exact ih rest (by omega) _ _ after value (clean _) next.1 next.2 known tail
        | node request continuation =>
            cases selected : lookupNode width request before.native with
            | mk selection chosen =>
              have chosenEdges : chosen.edges = before.native.edges := by
                simpa only [selected] using node_edges request before.native
              have chosenKnown : Recorded chosen := by
                intro handle original result stored
                exact known handle original result (chosenEdges ▸ stored)
              cases selection with
              | direct actual =>
                  have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,lift] using one)
                  rcases same with ⟨rfl,rfl⟩
                  exact ih rest (by omega) _ _ after value
                    (bodyCode_bind _ _ (compileNode_bodyCode actual) clean) next.1 next.2 chosenKnown tail
              | memoized handle =>
                cases demanded : demandNode handle chosen with
                | mk observation running =>
                  have runningEdges : running.edges = chosen.edges := by
                    simpa only [demanded] using demand_node_edges handle chosen
                  have runningKnown : Recorded running := by
                    intro handle original result stored
                    exact chosenKnown handle original result (runningEdges ▸ stored)
                  cases observation with
                  | absent | busy =>
                      simp only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] at one
                      cases one
                  | ready result =>
                      have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] using one)
                      rcases same with ⟨rfl,rfl⟩
                      exact ih rest (by omega) _ _ after value (clean result) next.1 next.2 runningKnown tail
                  | evaluate actual =>
                      have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] using one)
                      rcases same with ⟨rfl,rfl⟩
                      obtain ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest
                        (.code (compileNode actual)) (fun result => .finishNode handle result (continuation result))
                        ⟨running,before.operations⟩ after value tail
                      have bodyFields := fields_before_bind _ _ _ next.2
                      have bodyKnown := ih inner (by omega) _ _ current result (compileNode_bodyCode actual)
                        next.1 bodyFields runningKnown bodyTrace
                      have finishFacts := effects (bodyTrace.bind (fun result => .finishNode handle result (continuation result))) next.1 next.2
                      cases frameTrace with
                      | cons _ _ chosen reached _ _ count frameInputs frameStep remaining =>
                          obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                          have finished := yielded finishFacts.1 finishFacts.2.2.2.2 frameInputs frameStep
                          exact ih count (by omega) _ _ after value (clean result) finished.1 finished.2 bodyKnown remaining
        | edge request continuation =>
            cases selected : lookupEdge width request before.native with
            | mk handle chosen =>
              have chosenKnown := recorded_lookup before.native request known
              simp only [selected] at chosenKnown
              cases demanded : demandEdge handle chosen with
              | mk observation running =>
                have runningKnown := recorded_demand chosen handle chosenKnown
                simp only [demanded] at runningKnown
                cases observation with
                | absent | busy => simp only [step,selected,demanded] at one; cases one
                | ready result =>
                    have same := Outcome.yielded.inj (by simpa only [step,selected,demanded] using one)
                    rcases same with ⟨rfl,rfl⟩
                    exact ih rest (by omega) _ _ after value (clean result) next.1 next.2 runningKnown tail
                | evaluate actual =>
                    have same := Outcome.yielded.inj (by simpa only [step,selected,demanded] using one)
                    rcases same with ⟨rfl,rfl⟩
                    obtain ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest
                      (.edgeBody actual .pure) (fun result => .finishEdge handle result (continuation result))
                      ⟨running,before.operations⟩ after value tail
                    have bodyFields := fields_before_bind _ _ _ next.2
                    have bodyKnown := ih inner (by omega) _ _ current result (by intro value; trivial)
                      next.1 bodyFields runningKnown bodyTrace
                    have owner := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2
                    have protected := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner inner handle actual
                      ⟨running,before.operations⟩ current result next.1.native.shape owner bodyTrace.steps
                    have finishFacts := effects (bodyTrace.bind (fun result => .finishEdge handle result (continuation result))) next.1 next.2
                    cases frameTrace with
                    | cons _ _ chosen reached _ _ count frameInputs frameStep remaining =>
                        obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                        have writer : Writer (width := width) actual result :=
                          ⟨handle,⟨running,before.operations⟩,current,inner,next.1,bodyFields.1,owner,bodyTrace,protected.1,
                            .cons _ _ _ _ _ _ _ frameInputs rfl (.refl _ _)⟩
                        have finished := yielded finishFacts.1 finishFacts.2.2.2.2 frameInputs frameStep
                        have finishedKnown := recorded_finish current.native handle actual result bodyKnown protected.1 writer
                        exact ih count (by omega) _ _ after value (clean result) finished.1 finished.2 finishedKnown remaining

/-- Empty native tables derive every returned edge's earlier literal body and finish. -/
theorem completed {A : Type} (control : Control A) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (fuel : Nat) (value : A) (after : Checked width)
    (clean : Clean control) (good : Good (⟨initial width machine,operations⟩ : Checked width))
    (fields : Fields control (⟨initial width machine,operations⟩ : Checked width))
    (trace : Trace fuel control ⟨initial width machine,operations⟩ (.code (.pure value)) after) :
    ∀ handle request result, after.native.edges.cells handle = some ⟨request,.returned result⟩ →
      Writer (width := width) request result := by
  apply preserves fuel control _ after value clean good fields _ trace
  intro handle request result absent
  cases absent

end MicroCFTA.SourceCurrentNativeEdgeHistory
