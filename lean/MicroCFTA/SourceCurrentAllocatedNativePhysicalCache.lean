import MicroCFTA.SourceEqualityNativeDemandCellValidity
import MicroCFTA.SourceRecursiveIntersectionNativeObservations
import MicroCFTA.SourceRecursiveIntersectionNativeShape

/-!
# Physical validity of checked native memo cells

Every cell retains its original available operands and checked physical key.
Returned node cells retain available values. Returned edge cells retain resident rows.
These conditions do not assert a result language or completed body execution.
Completion needs only its actual running cell and the returned physical record.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

/-- All node phases retain original operands. Returned values remain available. -/
def NodeGood (machine : Machine Symbol Guard)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard)) : Prop :=
  NodeReady machine cell.request ∧ match cell.status with
    | .returned value => Available machine.heap value
    | _ => True

/-- All edge phases retain original rows. Returned rows remain resident. -/
def EdgeGood (machine : Machine Symbol Guard)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)) : Prop :=
  EdgeReady machine cell.request ∧ match cell.status with
    | .returned value => EdgeResident machine.heap value
    | _ => True

/-- Physical validity includes exact original keys, fresh handles, and resident results. -/
structure Valid (state : Native width Symbol Guard) : Prop where
  machine : SourceRecursiveIntersectionKernel.Valid state.machine
  nodes : FlatMemoThunk.Valid (NodeKey width) (NodeGood state.machine) state.nodes
  edges : FlatMemoThunk.Valid (EdgeKeyOf width) (EdgeGood state.machine) state.edges

/-- An actual valid machine admits empty physical memo tables. -/
theorem initial_valid (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) : Valid (initial width machine) :=
  ⟨valid, FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Physical validity supplies the structural key and fresh-handle invariant. -/
theorem Valid.shape {state : Native width Symbol Guard} (valid : Valid state) :
    SourceRecursiveIntersectionNative.Shape state := by
  constructor
  · exact ⟨valid.nodes.bounded, fun key handle stored => by
      obtain ⟨cell, present, linked⟩ := valid.nodes.linked key handle stored
      exact ⟨cell, present, linked.1⟩, fun _ _ _ => trivial⟩
  · exact ⟨valid.edges.bounded, fun key handle stored => by
      obtain ⟨cell, present, linked⟩ := valid.edges.linked key handle stored
      exact ⟨cell, present, linked.1⟩, fun _ _ _ => trivial⟩

/-- Physical and domain growth retain original node inputs and returned availability. -/
theorem NodeGood.grows
    {before after : Machine Symbol Guard}
    {cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard)}
    (good : NodeGood before cell) (growth : Extension before after) :
    NodeGood after cell := by
  refine ⟨⟨good.1.1.grows _ growth, growth.available _ good.1.2.1, growth.available _ good.1.2.2⟩, ?_⟩
  cases phase : cell.status with
  | suspended | evaluating => trivial
  | returned value =>
      have available := good.2
      rw [phase] at available
      exact growth.available _ available

/-- Physical and domain growth retain complete original rows and returned residency. -/
theorem EdgeGood.grows
    {before after : Machine Symbol Guard}
    {cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)}
    (good : EdgeGood before cell) (growth : Extension before after) :
    EdgeGood after cell := by
  refine ⟨⟨good.1.1.grows _ growth, edge_grows _ _ growth.heap _ good.1.2.1,
    edge_grows _ _ growth.heap _ good.1.2.2⟩, ?_⟩
  cases phase : cell.status with
  | suspended | evaluating => trivial
  | returned value =>
      have resident := good.2
      rw [phase] at resident
      exact edge_grows _ _ growth.heap _ resident

/-- Actual machine growth retains both checked memo families and their original inputs. -/
theorem advance_valid
    (state : Native width Symbol Guard) (valid : Valid state)
    (after : Machine Symbol Guard) (checked : SourceRecursiveIntersectionKernel.Valid after)
    (growth : Extension state.machine after) : Valid (advance state after) :=
  ⟨checked, FlatMemoThunk.Valid.map _ _ _ _ valid.nodes (fun _ good => good.grows growth),
    FlatMemoThunk.Valid.map _ _ _ _ valid.edges (fun _ good => good.grows growth)⟩

/-- Node publication checks current original inputs and the source word range. -/
theorem lookupNode_valid
    (state : Native width Symbol Guard) (valid : Valid state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    Valid (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using valid
  | some value =>
      simp only [lookupNode, key]
      exact ⟨valid.machine, FlatMemoThunk.lookup_valid value request state.nodes _ _ valid.nodes
        ⟨key, safe⟩ ⟨ready, trivial⟩, valid.edges⟩

/-- Edge publication checks complete current rows and their original source word range. -/
theorem lookupEdge_valid
    (state : Native width Symbol Guard) (valid : Valid state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    Valid (lookupEdge width request state).2 :=
  ⟨valid.machine, valid.nodes, FlatMemoThunk.lookup_valid _ request state.edges _ _ valid.edges
    ⟨rfl, safe⟩ ⟨ready, trivial⟩⟩

/-- Node demand retains every original input and returned availability. -/
theorem demandNode_valid
    (state : Native width Symbol Guard) (valid : Valid state) (handle : Nat) :
    Valid (demandNode handle state).2 := by
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
theorem demandEdge_valid
    (state : Native width Symbol Guard) (valid : Valid state) (handle : Nat) :
    Valid (demandEdge handle state).2 := by
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
theorem finishNode_valid
    (state : Native width Symbol Guard) (valid : Valid state)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.machine.heap value) :
    Valid (SourceRecursiveIntersectionThunks.finishNode handle value state) := by
  have good := valid.nodes.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle (.returned value) state.nodes _ _
    valid.nodes _ running ⟨good.1, available⟩, valid.edges⟩

/-- Completion stores a resident row at its original running edge handle. -/
theorem finishEdge_valid
    (state : Native width Symbol Guard) (valid : Valid state)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (resident : EdgeResident state.machine.heap value) :
    Valid (SourceRecursiveIntersectionThunks.finishEdge handle value state) := by
  have good := valid.edges.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle (.returned value) state.edges _ _
    valid.edges _ running ⟨good.1, resident⟩⟩

/-- Checked node words and complete resident originals identify the request actually stored at a hit. -/
theorem node_request_exact
    (state : Native width Symbol Guard) (valid : Valid state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard))
    (stored : state.nodes.cells handle = some cell) : cell.request = request := by
  obtain ⟨original, present, originalKey⟩ := valid.nodes.linked key handle published
  have same : original = cell := Option.some.inj (present.symm.trans stored)
  subst original
  have good := valid.nodes.checked handle cell stored
  exact NodeRequest.components _ _ (SourceRecursiveIntersectionMemo.requestKey_injective width state.machine valid.machine
    cell.request.domain request.domain cell.request.left cell.request.right request.left request.right good.1.1 ready.1
    originalKey.2 checked.2 good.1.2.1 good.1.2.2 ready.2.1 ready.2.2 (originalKey.1.trans checked.1.symm))

/-- Checked raw edge words identify the original domain and complete ordered row payloads. -/
theorem edge_request_exact
    (state : Native width Symbol Guard) (valid : Valid state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : EdgeKeyOf width request key)
    (handle : Nat) (published : state.edges.table key = some handle)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard))
    (stored : state.edges.cells handle = some cell) : cell.request = request := by
  obtain ⟨original, present, originalKey⟩ := valid.edges.linked key handle published
  have same : original = cell := Option.some.inj (present.symm.trans stored)
  subst original
  have good := valid.edges.checked handle cell stored
  exact EdgeRequest.components _ _ (SourceRecursiveIntersectionEdgeMemo.requestKey_injective width state.machine valid.machine
    cell.request.domain request.domain cell.request.left cell.request.right request.left request.right good.1.1 ready.1
    originalKey.2 checked.2 good.1.2.1 good.1.2.2 ready.2.1 ready.2.2 (originalKey.1.trans checked.1.symm))


/-- A completed node hit retains the exact original request and returns an available value without effects. -/
theorem node_ready_receipt
    (state : Native width Symbol Guard) (valid : Valid state)
    (request original : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle) (value : Value Symbol Guard)
    (stored : state.nodes.cells handle = some ⟨original, .returned value⟩) :
    original = request ∧ lookupNode width request state = (.memoized handle, state) ∧
      demandNode handle state = (.ready value, state) ∧ Available state.machine.heap value := by
  have same := node_request_exact state valid request ready key checked handle published _ stored
  change original = request at same
  refine ⟨same, ?_, ?_, (valid.nodes.checked handle _ stored).2⟩
  · simp only [lookupNode, checked.1, FlatMemoThunk.lookupOrInsert, published]
  · simp only [demandNode, FlatMemoThunk.demand, stored]

/-- A completed edge hit retains the exact original rows and returns a resident row without effects. -/
theorem edge_ready_receipt
    (state : Native width Symbol Guard) (valid : Valid state)
    (request original : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : EdgeKeyOf width request key)
    (handle : Nat) (published : state.edges.table key = some handle) (value : EdgeValue Symbol Guard)
    (stored : state.edges.cells handle = some ⟨original, .returned value⟩) :
    original = request ∧ lookupEdge width request state = (handle, state) ∧
      demandEdge handle state = (.ready value, state) ∧ EdgeResident state.machine.heap value := by
  have same := edge_request_exact state valid request ready key checked handle published _ stored
  change original = request at same
  refine ⟨same, ?_, ?_, (valid.edges.checked handle _ stored).2⟩
  · simp only [lookupEdge, checked.1, FlatMemoThunk.lookupOrInsert, published]
  · simp only [demandEdge, FlatMemoThunk.demand, stored]

/-- Actual node lookup and ready demand derive current result availability and exact requested operands. -/
theorem node_ready
    (request : NodeRequest Symbol Guard) (before chosen after : Native width Symbol Guard)
    (handle : Nat) (value : Value Symbol Guard) (valid : Valid before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready value, after)) :
    chosen.nodes.cells handle = some ⟨request, .returned value⟩ ∧ after = chosen ∧
      Available after.machine.heap value := by
  have chosenValid := lookupNode_valid before valid request ready safe
  simp only [selected] at chosenValid
  obtain ⟨key, requested, published, sameMachine⟩ :=
    SourceRecursiveIntersectionNative.lookupNode_memoized request before chosen handle selected
  have chosenReady : NodeReady chosen.machine request := by rw [sameMachine]; exact ready
  obtain ⟨original, stored, unchanged⟩ :=
    SourceRecursiveIntersectionNative.demandNode_ready handle chosen after value demanded
  have receipt := node_ready_receipt chosen chosenValid request original chosenReady key
    ⟨requested, safe⟩ handle published value stored
  rw [receipt.1] at stored
  exact ⟨stored, unchanged, by rw [unchanged]; exact receipt.2.2.2⟩

/-- Actual edge lookup and ready demand derive residency and the exact complete requested rows. -/
theorem edge_ready
    (request : EdgeRequest Symbol Guard) (before chosen after : Native width Symbol Guard)
    (handle : Nat) (value : EdgeValue Symbol Guard) (valid : Valid before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready value, after)) :
    chosen.edges.cells handle = some ⟨request, .returned value⟩ ∧ after = chosen ∧
      EdgeResident after.machine.heap value := by
  have chosenValid := lookupEdge_valid before valid request ready safe
  simp only [selected] at chosenValid
  obtain ⟨published, sameMachine⟩ :=
    SourceRecursiveIntersectionNative.lookupEdge_selected request before chosen handle selected
  have chosenReady : EdgeReady chosen.machine request := by rw [sameMachine]; exact ready
  obtain ⟨original, stored, unchanged⟩ :=
    SourceRecursiveIntersectionNative.demandEdge_ready handle chosen after value demanded
  have receipt := edge_ready_receipt chosen chosenValid request original chosenReady _
    ⟨rfl, safe⟩ handle published value stored
  rw [receipt.1] at stored
  exact ⟨stored, unchanged, by rw [unchanged]; exact receipt.2.2.2⟩

/-- An actual node start selects the complete requested operands from physical validity alone. -/
theorem node_started
    (request actual : NodeRequest Symbol Guard) (before chosen running : Native width Symbol Guard)
    (handle : Nat) (valid : Valid before) (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, running)) : actual = request := by
  have chosenValid := lookupNode_valid before valid request ready safe
  simp only [selected] at chosenValid
  obtain ⟨key, requested, published, sameMachine⟩ :=
    SourceRecursiveIntersectionNative.lookupNode_memoized request before chosen handle selected
  have chosenReady : NodeReady chosen.machine request := by rw [sameMachine]; exact ready
  have suspended := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).1
  exact node_request_exact chosen chosenValid request chosenReady key ⟨requested, safe⟩ handle published _ suspended

/-- An actual edge start selects the requested complete row pair from physical validity alone. -/
theorem edge_started
    (request actual : EdgeRequest Symbol Guard) (before chosen running : Native width Symbol Guard)
    (handle : Nat) (valid : Valid before) (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.evaluate actual, running)) : actual = request := by
  have chosenValid := lookupEdge_valid before valid request ready safe
  simp only [selected] at chosenValid
  obtain ⟨published, sameMachine⟩ :=
    SourceRecursiveIntersectionNative.lookupEdge_selected request before chosen handle selected
  have chosenReady : EdgeReady chosen.machine request := by rw [sameMachine]; exact ready
  have suspended := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).1
  exact edge_request_exact chosen chosenValid request chosenReady _ ⟨rfl, safe⟩ handle published _ suspended

/-- Physical validity suffices to retain all running cells through node lookup. -/
theorem lookupNode_retains (state : Native width Symbol Guard) (valid : Valid state)
    (request : NodeRequest Symbol Guard) :
    SourceRecursiveIntersectionNative.Retains state (lookupNode width request state).2 :=
  SourceRecursiveIntersectionNative.lookupNode_retains request state valid.shape

/-- Physical validity suffices to retain all running cells through edge lookup. -/
theorem lookupEdge_retains (state : Native width Symbol Guard) (valid : Valid state)
    (request : EdgeRequest Symbol Guard) :
    SourceRecursiveIntersectionNative.Retains state (lookupEdge width request state).2 :=
  SourceRecursiveIntersectionNative.lookupEdge_retains request state valid.shape

/-- Node demand retains every running cell, without a result property. -/
theorem demandNode_retains (state : Native width Symbol Guard) (handle : Nat) :
    SourceRecursiveIntersectionNative.Retains state (demandNode handle state).2 :=
  SourceRecursiveIntersectionNative.demandNode_retains handle state

/-- Edge demand retains every running cell, without a result property. -/
theorem demandEdge_retains (state : Native width Symbol Guard) (handle : Nat) :
    SourceRecursiveIntersectionNative.Retains state (demandEdge handle state).2 :=
  SourceRecursiveIntersectionNative.demandEdge_retains handle state

/-- Machine effects leave all memo phases and original requests unchanged. -/
theorem advance_retains (state : Native width Symbol Guard) (after : Machine Symbol Guard) :
    SourceRecursiveIntersectionNative.Retains state (advance state after) :=
  ⟨FlatMemoThunk.Running.refl _, FlatMemoThunk.Running.refl _⟩

/-- Finishing a node retains every different running node cell. -/
theorem finishNode_running_other (state : Native width Symbol Guard) (handle other : Nat)
    (value : Value Symbol Guard) (request : NodeRequest Symbol Guard) (different : other ≠ handle)
    (running : state.nodes.cells other = some ⟨request, .evaluating⟩) :
    (SourceRecursiveIntersectionThunks.finishNode handle value state).nodes.cells other =
      some ⟨request, .evaluating⟩ :=
  FlatMemoThunk.finish_running_other handle other value state.nodes request different running

/-- Finishing an edge retains every different running edge cell. -/
theorem finishEdge_running_other (state : Native width Symbol Guard) (handle other : Nat)
    (value : EdgeValue Symbol Guard) (request : EdgeRequest Symbol Guard) (different : other ≠ handle)
    (running : state.edges.cells other = some ⟨request, .evaluating⟩) :
    (SourceRecursiveIntersectionThunks.finishEdge handle value state).edges.cells other =
      some ⟨request, .evaluating⟩ :=
  FlatMemoThunk.finish_running_other handle other value state.edges request different running

/-- Checked execution provenance implies physical validity. Lifecycle laws do not use this implication. -/
theorem of_provenance
    [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {holds : SourceSymbolicIndex.Constraint FullSyntax.Formula →
      Language.Term (SourceObservations.Label FullSyntax.Formula) → Bool}
    {state : Native width (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula)}
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state) : Valid state := by
  refine ⟨valid.machine, ?_, ?_⟩
  · refine FlatMemoThunk.Valid.map _ _ _ _ valid.nodes ?_
    intro cell good
    refine ⟨good.1, ?_⟩
    cases phase : cell.status with
    | suspended | evaluating => trivial
    | returned value =>
        have produced := good.2
        rw [phase] at produced
        exact produced.spec.2.1
  · refine FlatMemoThunk.Valid.map _ _ _ _ valid.edges ?_
    intro cell good
    refine ⟨good.1, ?_⟩
    cases phase : cell.status with
    | suspended | evaluating => trivial
    | returned value =>
        have produced := good.2
        rw [phase] at produced
        exact produced.spec.2.1

end MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
