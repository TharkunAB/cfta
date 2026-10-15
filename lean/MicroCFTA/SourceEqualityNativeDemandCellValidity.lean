import MicroCFTA.SourceEqualityNativeDemandProvenance

/-!
# Lifecycle of checked native cell provenance

Publication retains original available inputs and explicit word bounds.
Demand preserves these facts in both memo families. Completion uses an
actual checked-body receipt. Ready hits recover that receipt and the exact
original request without replaying its physical effects.
-/
namespace MicroCFTA.SourceEqualityNativeDemandProvenance
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}

/-- Physical and domain growth retain original node inputs and actual completed receipts. -/
theorem NodeGood.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {before after : Machine Symbol Guard}
    {cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard)}
    (good : NodeGood (width := width) holds before cell) (growth : Extension before after) :
    NodeGood (width := width) holds after cell := by
  refine ⟨⟨good.1.1.grows _ growth, growth.available _ good.1.2.1, growth.available _ good.1.2.2⟩, ?_⟩
  cases phase : cell.status with
  | suspended | evaluating => trivial
  | returned value =>
      have produced := good.2
      rw [phase] at produced
      exact produced.grows growth

/-- Physical and domain growth retain complete original rows and checked completed receipts. -/
theorem EdgeGood.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {before after : Machine Symbol Guard}
    {cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)}
    (good : EdgeGood (width := width) holds before cell) (growth : Extension before after) :
    EdgeGood (width := width) holds after cell := by
  refine ⟨⟨good.1.1.grows _ growth, edge_grows _ _ growth.heap _ good.1.2.1,
    edge_grows _ _ growth.heap _ good.1.2.2⟩, ?_⟩
  cases phase : cell.status with
  | suspended | evaluating => trivial
  | returned value =>
      have produced := good.2
      rw [phase] at produced
      exact produced.grows growth

/-- Actual machine growth retains both checked memo families and their original receipts. -/
theorem advance_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
    (after : Machine Symbol Guard) (checked : SourceRecursiveIntersectionKernel.Valid after)
    (growth : Extension state.machine after) : Valid holds (advance state after) :=
  ⟨checked, FlatMemoThunk.Valid.map _ _ _ _ valid.nodes (fun _ good => good.grows growth),
    FlatMemoThunk.Valid.map _ _ _ _ valid.edges (fun _ good => good.grows growth)⟩

/-- Node publication checks current original inputs and the source word range. -/
theorem lookupNode_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    Valid holds (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using valid
  | some value =>
      simp only [lookupNode, key]
      exact ⟨valid.machine, FlatMemoThunk.lookup_valid value request state.nodes _ _ valid.nodes
        ⟨key, safe⟩ ⟨ready, trivial⟩, valid.edges⟩

/-- Edge publication checks complete current rows and their original source word range. -/
theorem lookupEdge_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    Valid holds (lookupEdge width request state).2 :=
  ⟨valid.machine, valid.nodes, FlatMemoThunk.lookup_valid _ request state.edges _ _ valid.edges
    ⟨rfl, safe⟩ ⟨ready, trivial⟩⟩

/-- Node demand retains every original input and existing checked receipt. -/
theorem demandNode_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state) (handle : Nat) :
    Valid holds (demandNode handle state).2 := by
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

/-- Edge demand retains both native families and every actual checked receipt. -/
theorem demandEdge_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state) (handle : Nat) :
    Valid holds (demandEdge handle state).2 := by
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

/-- Completion installs a checked node receipt only in the original running cell. -/
theorem finishNode_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (produced : NodeProduced (width := width) holds state.machine request value) :
    Valid holds (SourceRecursiveIntersectionThunks.finishNode handle value state) := by
  have good := valid.nodes.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle (.returned value) state.nodes _ _
    valid.nodes _ running ⟨good.1, produced⟩, valid.edges⟩

/-- Completion installs a checked edge receipt only at its original running handle. -/
theorem finishEdge_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (produced : EdgeProduced (width := width) holds state.machine request value) :
    Valid holds (SourceRecursiveIntersectionThunks.finishEdge handle value state) := by
  have good := valid.edges.checked handle _ running
  simp only [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle (.returned value) state.edges _ _
    valid.edges _ running ⟨good.1, produced⟩⟩

/-- Checked node words and complete resident originals identify the request actually stored at a hit. -/
theorem node_request_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
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
theorem edge_request_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
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

/-- A completed node hit returns its original checked receipt and available result without effects. -/
theorem node_ready_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
    (request original : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle) (value : Value Symbol Guard)
    (stored : state.nodes.cells handle = some ⟨original, .returned value⟩) :
    lookupNode width request state = (.memoized handle, state) ∧ demandNode handle state = (.ready value, state) ∧
      NodeProduced (width := width) holds state.machine request value ∧
      Available state.machine.heap value ∧ NodeMeaning holds request value := by
  have same := node_request_exact state valid request ready key checked handle published _ stored
  change original = request at same
  subst original
  have produced := (valid.nodes.checked handle _ stored).2
  exact ⟨by simp only [lookupNode, checked.1, FlatMemoThunk.lookupOrInsert, published],
    by simp only [demandNode, FlatMemoThunk.demand, stored], produced, produced.spec.2⟩

/-- A completed edge hit returns the actual checked receipt and resident result without effect replay. -/
theorem edge_ready_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} (state : Native width Symbol Guard) (valid : Valid holds state)
    (request original : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : EdgeKeyOf width request key)
    (handle : Nat) (published : state.edges.table key = some handle) (value : EdgeValue Symbol Guard)
    (stored : state.edges.cells handle = some ⟨original, .returned value⟩) :
    lookupEdge width request state = (handle, state) ∧ demandEdge handle state = (.ready value, state) ∧
      EdgeProduced (width := width) holds state.machine request value ∧
      EdgeResident state.machine.heap value ∧ EdgeMeaning holds request value := by
  have same := edge_request_exact state valid request ready key checked handle published _ stored
  change original = request at same
  subst original
  have produced := (valid.edges.checked handle _ stored).2
  exact ⟨by simp only [lookupEdge, checked.1, FlatMemoThunk.lookupOrInsert, published],
    by simp only [demandEdge, FlatMemoThunk.demand, stored], produced, produced.spec.2⟩

end MicroCFTA.SourceEqualityNativeDemandProvenance
