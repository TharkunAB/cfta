import MicroCFTA.SourceCurrentNativeRowOrigins
import MicroCFTA.SourceCurrentNativeEdgeHistory
import MicroCFTA.SourceCurrentAllocatedQueryMemo
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo

/-!
# Persistent native edge writer histories

The history starts with empty native memo tables. Each later event is an
exact physical advance or an actual completed checked trace. The producer
retains the earlier literal body and finish of each returned edge cell.
The trace premise records past execution. It does not produce completion.
-/
namespace MicroCFTA.SourceCurrentNativeEdgeWriterHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse effects fields_before_bind Walk)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentNativeEdgeHistory (Writer)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

private theorem node_edges (request : NodeRequest Symbol Guard) (state : Native width Symbol Guard) :
    (lookupNode width request state).2.edges = state.edges := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right <;>
    simp only [lookupNode,key]

private theorem demand_node_edges (handle : Nat) (state : Native width Symbol Guard) :
    (demandNode handle state).2.edges = state.edges := rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

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
          exact ih rest (by omega) resume middle after value nextClean next.1 next.2 (same ▸ known) tail
      | code code =>
        cases code with
        | pure | fail => cases one
        | finishNode | finishEdge => cases clean
        | work job continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (run job before.native.machine.heap).1)) _ after value (clean _) next.1 next.2 known tail
        | enter domain left right first second continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second).1)) _ after value (clean _) next.1 next.2 known tail
        | read name continuation =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih rest (by omega) (.code (continuation (SourcePreparedSharedRows.read before.native.machine.heap name))) _ after value (clean _) next.1 next.2 known tail
        | optionalBinder pair body continuation =>
            cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
            | pending key heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                cases one
            | done result heap =>
                simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
                obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
                exact ih rest (by omega) (.code (continuation result)) _ after value (clean _) next.1 next.2 known tail
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
                  exact ih rest (by omega) (.code ((compileNode actual).bind continuation)) _ after value
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
                      exact ih rest (by omega) (.code (continuation result)) _ after value (clean result) next.1 next.2 runningKnown tail
                  | evaluate actual =>
                      have same := Outcome.yielded.inj (by simpa only [step,SourceRecursiveIntersectionNative.step,selected,demanded,lift] using one)
                      rcases same with ⟨rfl,rfl⟩
                      obtain ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest
                        (.code (compileNode actual)) (fun result => .finishNode handle result (continuation result))
                        ⟨running,before.operations⟩ after value tail
                      have bodyFields := fields_before_bind (.code (compileNode actual))
                        (fun result => .finishNode handle result (continuation result)) _ next.2
                      have bodyKnown := ih inner (by omega) (.code (compileNode actual)) _ current result (compileNode_bodyCode actual)
                        next.1 bodyFields runningKnown bodyTrace
                      have finishFacts := effects (bodyTrace.bind (fun result => .finishNode handle result (continuation result))) next.1 next.2
                      cases frameTrace with
                      | cons _ _ chosen reached _ _ count frameInputs frameStep remaining =>
                          obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                          have finished := yielded finishFacts.1 finishFacts.2.2.2.2 frameInputs frameStep
                          exact ih count (by omega) (.code (continuation result)) _ after value (clean result) finished.1 finished.2 bodyKnown remaining
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
                    exact ih rest (by omega) (.code (continuation result)) _ after value (clean result) next.1 next.2 runningKnown tail
                | evaluate actual =>
                    have same := Outcome.yielded.inj (by simpa only [step,selected,demanded] using one)
                    rcases same with ⟨rfl,rfl⟩
                    obtain ⟨inner,outer,result,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest
                      (.edgeBody actual .pure) (fun result => .finishEdge handle result (continuation result))
                      ⟨running,before.operations⟩ after value tail
                    have bodyFields := fields_before_bind (.edgeBody actual .pure)
                      (fun result => .finishEdge handle result (continuation result)) _ next.2
                    have bodyKnown := ih inner (by omega) (.edgeBody actual .pure) _ current result (by intro value; trivial)
                      next.1 bodyFields runningKnown bodyTrace
                    have owner := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2
                    have ownerKept := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner inner handle actual
                      ⟨running,before.operations⟩ current result next.1.native.shape owner bodyTrace.steps
                    have finishFacts := effects (bodyTrace.bind (fun result => .finishEdge handle result (continuation result))) next.1 next.2
                    cases frameTrace with
                    | cons _ _ chosen reached _ _ count frameInputs frameStep remaining =>
                        obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                        have writer : Writer (width := width) actual result :=
                          ⟨handle,⟨running,before.operations⟩,current,inner,next.1,bodyFields.1,owner,bodyTrace,ownerKept.1,
                            .cons _ _ _ _ _ _ _ frameInputs rfl (.refl _ _)⟩
                        have finished := yielded finishFacts.1 finishFacts.2.2.2.2 frameInputs frameStep
                        have finishedKnown := recorded_finish current.native handle actual result bodyKnown ownerKept.1 writer
                        exact ih count (by omega) (.code (continuation result)) _ after value (clean result) finished.1 finished.2 finishedKnown remaining

/-- Past checked traces and literal physical advances retain the same persistent native tables. -/
inductive History : Checked width → Prop where
  /-- Empty native tables have no earlier returned cells. -/
  | initial (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State) :
      History ⟨initial width machine,operations⟩
  /-- A literal physical advance leaves every native edge cell unchanged. -/
  | advance {before : Checked width} (earlier : History before) (after : Physical) :
      History (SourceCurrentAllocatedQueryMemo.advancePhysical before after)
  /-- A completed clean checked trace records its actual past instructions. -/
  | trace {A : Type} {before after : Checked width} (earlier : History before)
      (control : Control A) (fuel : Nat) (value : A)
      (clean : Clean control) (good : Good before) (fields : Fields control before)
      (actual : Trace fuel control before (.code (.pure value)) after) : History after

/-- Every returned cell in a produced persistent history has an actual earlier writer. -/
theorem History.writers {state : Checked width} (history : History state) :
    ∀ handle request result, state.native.edges.cells handle = some ⟨request,.returned result⟩ →
      Writer (width := width) request result := by
  induction history with
  | initial machine operations => intro handle request result impossible; cases impossible
  | advance earlier after ih => exact ih
  | trace earlier control fuel value clean good fields actual ih =>
      exact preserves fuel control _ _ value clean good fields ih actual

/-- A completed query extends the earlier history without a caller-supplied clean-code certificate. -/
theorem History.query {before after : Checked width} (history : History before)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (value : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right))
      before (.code (.pure value)) after) : History after :=
  .trace history _ fuel value (by intro value; trivial) good (by intro value; trivial) actual

/-- A completed literal edge call recovers the writer of its result, including a ready hit. -/
theorem History.request {before after : Checked width} (history : History before)
    (request : EdgeRequest Symbol Guard) (fuel : Nat) (result : EdgeValue Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (requestEdge request.domain request.left request.right))
      before (.code (.pure result)) after) : Writer (width := width) request result := by
  have fields : Fields (.code (requestEdge request.domain request.left request.right)) before := fun _ => trivial
  cases actual with
  | cons _ _ resume middle _ _ rest inputs one tail =>
    have next := yielded good fields inputs one
    cases selected : lookupEdge width request before.native with
    | mk handle chosen =>
      have chosenKnown := recorded_lookup before.native request history.writers
      simp only [selected] at chosenKnown
      cases demanded : demandEdge handle chosen with
      | mk observation running =>
        cases observation with
        | absent | busy => simp only [step, requestEdge, selected, demanded] at one; cases one
        | ready value =>
          have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before.native chosen running handle value
            good.native inputs.1 inputs.2 selected demanded
          have same := Outcome.yielded.inj (by simpa only [step,requestEdge,selected,demanded] using one)
          rcases same with ⟨rfl,rfl⟩
          obtain ⟨_,same,_⟩ := pure_trace rest value result _ after tail.steps
          subst result
          exact chosenKnown handle request value receipt.1
        | evaluate original =>
          have originalSame := SourceCurrentAllocatedNativePhysicalCache.edge_started request original before.native chosen running handle
            good.native inputs.1 inputs.2 selected demanded
          subst original
          have same := Outcome.yielded.inj (by simpa only [step,requestEdge,selected,demanded] using one)
          rcases same with ⟨rfl,rfl⟩
          obtain ⟨inner,outer,value,current,total,bodyTrace,frameTrace⟩ := bind_inverse rest
            (.edgeBody request .pure) (fun value => .finishEdge handle value (.pure value))
            ⟨running,before.operations⟩ after result tail
          have bodyFields := fields_before_bind (.edgeBody request .pure)
            (fun value => .finishEdge handle value (.pure value)) _ next.2
          have owner := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running request demanded).2
          have ownerKept := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner inner handle request
            ⟨running,before.operations⟩ current value next.1.native.shape owner bodyTrace.steps
          cases frameTrace with
          | cons _ _ chosen reached _ _ count frameInputs frameStep remaining =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
            obtain ⟨_,same,_⟩ := pure_trace count value result _ after remaining.steps
            subst result
            exact ⟨handle,⟨running,before.operations⟩,current,inner,next.1,bodyFields.1,owner,bodyTrace,ownerKept.1,
              .cons _ _ _ _ _ _ _ frameInputs rfl (.refl _ _)⟩

/-- Each surviving row names indexed input rows and an earlier writer from the persistent history. -/
theorem History.rows {before after : Checked width} (history : History before)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (fuel : Nat) (result : Value Symbol Guard)
    (good : Good before)
    (actual : Trace fuel (.code (compileRows domain left right)) before (.code (.pure result)) after) :
    ∀ outputIndex output, (nodeEdges result)[outputIndex]? = some output →
      ∃ leftIndex rightIndex originalLeft originalRight,
        left[leftIndex]? = some originalLeft ∧ right[rightIndex]? = some originalRight ∧
        originalLeft.entry.key.symbol = originalRight.entry.key.symbol ∧
        Writer (width := width) ⟨domain,originalLeft,originalRight⟩ output ∧
        Value.empty ∉ output.children ∧
        output.entry.key.symbol = originalLeft.entry.key.symbol ∧
        output.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
          originalLeft.entry.key.constraint originalRight.entry.key.constraint := by
  obtain ⟨values,middle,count,walked,normalized,indexed⟩ := SourceCurrentNativeRowOrigins.rows
    domain left right fuel before after result good.native good.heap actual
  intro outputIndex output selected
  obtain ⟨scheduleIndex,leftIndex,rightIndex,originalLeft,originalRight,current,next,prefixFuel,childFuel,suffixFuel,
    found,input,leftFound,rightFound,symbols,counts,initialCalls,child,suffix⟩ := indexed outputIndex output selected
  have prefixFields : Fields (.code (SourceRecursiveIntersectionCode.walk
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
      ((pairs left right).take scheduleIndex))) before :=
    SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations _ _ (by intro pair member value; trivial)
  have prefixClean : Clean (.code (SourceRecursiveIntersectionCode.walk
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
      ((pairs left right).take scheduleIndex))) :=
    SourceRecursiveIntersectionBodyCode.bodyCode_walk _ _ (by intro pair member value; trivial)
  have currentHistory := History.trace history _ prefixFuel _ prefixClean good prefixFields initialCalls.trace
  have currentGood := (effects initialCalls.trace good prefixFields).1
  have writer := currentHistory.request ⟨domain,originalLeft,originalRight⟩ childFuel output currentGood child
  have live : Value.empty ∉ output.children := by
    have member : output ∈ canonicalEdges (surviving values) := by
      rw [normalized] at selected
      exact List.mem_of_getElem? selected
    have kept := (List.mem_filter.mp (canonicalEdges_member _ output member)).2
    intro emptyMember
    have anyEmpty : output.children.any (fun child => child.referenceOf == .empty) = true :=
      List.any_eq_true.mpr ⟨.empty,emptyMember,rfl⟩
    rw [anyEmpty] at kept
    cases kept
  obtain ⟨_,_,_,_,_,_,_,symbol,guard,_⟩ := writer.live live
  exact ⟨leftIndex,rightIndex,originalLeft,originalRight,leftFound,rightFound,symbols,writer,live,symbol,guard⟩

end MicroCFTA.SourceCurrentNativeEdgeWriterHistory
