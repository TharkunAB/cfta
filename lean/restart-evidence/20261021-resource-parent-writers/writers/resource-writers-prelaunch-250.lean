import MicroCFTA.SourceCurrentActualParentSelectedCertificates
import MicroCFTA.SourceCurrentActualParentNativeStores
import MicroCFTA.SourceCurrentEdgeCallNumeric
import MicroCFTA.FlatMemoThunkReturned

/-!
# Resource certificates at the same historical Parent writer

Cold calls retain one complete entry and its Parent execution.
Warm hits recover that certificate from the same returned cell.
This module treats one completed local call.
-/
namespace MicroCFTA.SourceCurrentResourceParentWriters
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeSupport" => SourceCurrentNativeRequestPositivePositions.Support
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "MergePositive" => SourceCurrentMergePositivePosition.Support
local notation "Normal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "History" => SourceCurrentNativeMuPublication.History
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {bits : Nat}

/-- One Parent writer retains its complete caller and entry resources. -/
def Written (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (request : EdgeRequest) (result : Edge) : Prop :=
  ∃ (g s r e p h m c n budget : Nat)
    (writerBefore : Caller (bits + 2)) (writerAfter : Checked (bits + 2))
    (savedFourth : Fourth) (savedMerge : Memo) (globals : Memos)
    (inventory : Inventory) (profile : Profile),
    SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      writerBefore.checked writerBefore.fourth writerBefore.merge = .done result writerAfter savedFourth savedMerge ∧
    Context formulas solver inventory writerBefore globals ∧
    Frame formulas solver inventory writerBefore.checked ∧ Fits profile writerBefore.checked ∧
    EqReady writerBefore.checked.operations.constraints request.inherited ∧
    EdgeResident writerBefore.checked.native.machine.heap request.value ∧
    (SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
      FieldAvailable writerBefore.checked.operations request.value.entry.key.constraint ∧
      EqReady writerBefore.checked.operations.constraints request.inherited ∧
      Values writerBefore.checked.native.machine.heap request.value.children) ∧
    SourceCurrentParentForecast.residentReserved bits budget request writerBefore.checked profile ∧
    Normal writerBefore.checked.native.machine.heap ∧
    NativeSupport writerBefore.checked.native.machine.heap writerBefore.checked.native ∧
    Nonempty (History empty writerBefore.checked.native.machine.heap) ∧
    MergeStored writerBefore.merge ∧ MergePositive writerBefore.merge

/-- Every returned edge cell retains its exact captured request and writer. -/
def Origins (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (state : Caller (bits + 2)) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (Written (bits := bits) formulas solver)) state.edgeResults

/-- Empty caller edge tables require no historical writer premise. -/
theorem initial (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (checked : Checked (bits + 2)) (memo : Memo) (fourth : Fourth) :
    Origins formulas solver (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  FlatMemoThunk.empty_valid _ _

private theorem begin_origins
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    (request : EdgeRequest) {before : Caller (bits + 2)}
    (origins : Origins formulas solver before) :
    Origins formulas solver (beginEdge request before).2.2 := by
  apply FlatMemoThunk.demand_spec
  exact FlatMemoThunk.lookup_valid _ _ _ _ _ origins rfl trivial

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem request_eq
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {globals : Memos} {before : Caller (bits + 2)}
    {first second : EdgeRequest}
    (context : Context formulas solver inventory before globals)
    (firstReady : EqReady before.checked.operations.constraints first.inherited)
    (firstResident : EdgeResident before.checked.native.machine.heap first.value)
    (secondReady : EqReady before.checked.operations.constraints second.inherited)
    (secondResident : EdgeResident before.checked.native.machine.heap second.value)
    (same : first.key = second.key) : first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _
    context.ready.good.operations.constraints first.inherited second.inherited firstReady secondReady
    (congrArg Prod.fst same)
  have values := edge_identity_unique _ context.ready.semantic.ready.semantic.1.normal.facts.coherent
    first.value second.value firstResident secondResident (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

private theorem finish_origins
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {before : Caller (bits + 2)} (handle : Nat) (owner : EdgeRequest) (value : Edge)
    (origins : Origins formulas solver before)
    (found : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (written : Written (bits := bits) formulas solver owner value) :
    Origins formulas solver (finishEdge handle value before) := by
  apply FlatMemoThunk.finish_spec
  · exact origins
  · intro request present
    have owners : owner = request := congrArg
      (fun cell : FlatMemoThunk.Cell EdgeRequest Edge => cell.request)
      (Option.some.inj (found.symm.trans present))
    exact owners ▸ written

private theorem body_written
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (globals : Memos)
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller (bits + 2)} {value : Edge}
    (actual : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget request before = .done value after)
    (context : Context formulas solver inventory before globals)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (reserved : SourceCurrentParentForecast.residentReserved bits budget request before.checked profile)
    (normal : Normal before.checked.native.machine.heap)
    (supported : NativeSupport before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap)
    (merged : MergeStored before.merge) (positiveMemo : MergePositive before.merge) :
    after.edgeResults = before.edgeResults ∧ Written (bits := bits) formulas solver request value := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge with
  | failed =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeBody, observed] at actual
      cases actual
  | done result checked fourth memo =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeBody, observed] at actual
      cases actual
      exact ⟨rfl, g, s, r, e, p, h, m, c, n, budget, before, checked, fourth, memo,
        globals, inventory, profile, observed, context, frame, fits, inherited, resident,
        (fun _ => ⟨context.ready.good.fields request.value.entry.key request.value resident, inherited,
          context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ _ resident⟩),
        reserved, normal, supported, ⟨causal⟩, merged, positiveMemo⟩

/-- A completed local call retains the resource witness from its actual cell. -/
theorem edge_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (globals : Memos)
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller (bits + 2)} {result : Edge}
    (actual : SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (context : Context formulas solver inventory before globals)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (reserved : SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile)
    (origins : Origins formulas solver before)
    (normal : Normal before.checked.native.machine.heap)
    (supported : NativeSupport before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap)
    (merged : MergeStored before.merge) (positiveMemo : MergePositive before.merge) :
    Origins formulas solver after ∧ Written (bits := bits) formulas solver request result := by
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  have prior := begin_origins request origins
  rw [started] at prior
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, merge, _fourth, _nodes⟩ := components
  have candidateReady : EqReady running.checked.operations.constraints request.inherited := by
    rw [checked]
    exact inherited
  have candidateResident : EdgeResident running.checked.native.machine.heap request.value := by
    rw [checked]
    exact resident
  cases action with
  | busy | absent =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeCall, started] at actual
      cases actual
  | ready value =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeCall, started] at actual
      cases actual
      let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
      have observed := congrArg (fun result => (result.2.1, result.2.2.edgeResults)) started
      change FlatMemoThunk.demand published.1 published.2 = (.ready value, running.edgeResults) at observed
      obtain ⟨owner, found, unchanged⟩ := FlatMemoThunk.demand_ready_original _ _ value _ observed
      have publishedOrigins := FlatMemoThunk.lookup_valid request.key request before.edgeResults
        (fun request key => request.key = key)
        (FlatMemoThunk.CellSpec (Written (bits := bits) formulas solver)) origins rfl trivial
      obtain ⟨cell, present, key⟩ := publishedOrigins.linked request.key published.1
        (FlatMemoThunk.lookup_stored _ _ _)
      have cells := Option.some.inj (present.symm.trans found)
      subst cell
      have written : Written (bits := bits) formulas solver owner value := publishedOrigins.checked _ _ found
      have retained : running.edgeResults.cells handle = some ⟨owner, .returned value⟩ := by
        have handles : published.1 = handle := congrArg Prod.fst started
        rw [← unchanged, handles] at found
        exact found
      have runningContext := (SourceCurrentAllocatedPartialCallSteps.edge_hit formulas solver
        context inherited resident started).1.context
      have ownerGood := runningContext.sound.edges _ _ retained
      have same := request_eq runningContext ownerGood.inherited ownerGood.input
        candidateReady candidateResident key
      exact ⟨prior, same ▸ written⟩
  | evaluate owner =>
      obtain ⟨runningContext, ownerGood, key, cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver context inherited resident started
      have same := request_eq runningContext ownerGood.inherited ownerGood.input
        candidateReady candidateResident key
      have runningFrame : Frame formulas solver inventory running.checked := by
        simpa only [checked] using frame
      have runningFits : Fits profile running.checked := by
        simpa only [checked] using fits
      have room : SourceCurrentParentForecast.residentReserved bits budget owner running.checked profile := by
        simpa only [SourceCurrentEdgeCallNumeric.Reserved, started] using reserved
      cases body : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget owner running with
      | failed =>
          simp only [SourceCurrentAllocatedPartialWorker.edgeCall, started, body,
            SourceCurrentAllocatedPartialWorker.Outcome.bind] at actual
          cases actual
      | done value middle =>
          simp only [SourceCurrentAllocatedPartialWorker.edgeCall, started, body,
            SourceCurrentAllocatedPartialWorker.Outcome.bind] at actual
          cases actual
          obtain ⟨tables, written⟩ := body_written formulas solver inventory profile globals body
            runningContext runningFrame runningFits ownerGood.inherited ownerGood.input room
            (by simpa only [checked] using normal) (by simpa only [checked] using supported)
            (by simpa only [checked] using causal) (by simpa only [merge] using merged)
            (by simpa only [merge] using positiveMemo)
          have middleOrigins : Origins formulas solver middle := by
            simpa only [Origins, tables] using prior
          have evaluating : middle.edgeResults.cells handle = some ⟨owner, .evaluating⟩ := by
            rw [tables]
            exact cell
          exact ⟨finish_origins handle owner value middleOrigins evaluating written, same ▸ written⟩

end MicroCFTA.SourceCurrentResourceParentWriters
