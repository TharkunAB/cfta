import MicroCFTA.SourceCurrentAllocatedNativeContextRebase
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache

/-!
# Causal request admission in every native memo phase

Every stored request retains admitted operands and covered seen-pair names.
This property applies to suspended, evaluating, and returned cells.
Lookup must establish coverage before it publishes a new request.
Demand and finish change only the phase of the original stored request.

The invariant has no result-language law. Physical key validity remains
separate. It identifies an original stored request with a requested hit.
Actual code execution must still derive each new request's coverage.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache (NodeInputs EdgeInputs)
open SourceCurrentAllocatedNativeContextRebase (SeenCovered SeenAdmitted)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {view : View Symbol}

/-- All stored cells retain the same request property in every phase. -/
def Requests (property : Request → Prop) (state : FlatMemoThunk.State Key Request Answer) : Prop :=
  ∀ handle cell, state.cells handle = some cell → property cell.request

/-- Empty memo tables have no request admission obligation. -/
theorem Requests.empty (property : Request → Prop) :
    Requests property (FlatMemoThunk.empty : FlatMemoThunk.State Key Request Answer) := by
  intro handle cell absent
  cases absent

/-- A hit keeps its original request. A miss publishes only the supplied admitted request. -/
theorem Requests.lookup [DecidableEq Key] (property : Request → Prop) (key : Key) (request : Request)
    (state : FlatMemoThunk.State Key Request Answer) (covered : Requests property state)
    (known : property request) : Requests property (FlatMemoThunk.lookupOrInsert key request state).2 := by
  cases found : state.table key with
  | some handle => simpa only [FlatMemoThunk.lookupOrInsert, found] using covered
  | none =>
      intro handle cell stored
      by_cases same : handle = state.next
      · subst handle
        have equal : (⟨request, .suspended⟩ : FlatMemoThunk.Cell Request Answer) = cell := by
          simpa [FlatMemoThunk.lookupOrInsert, found, Cache.put] using stored
        subst cell
        exact known
      · exact covered handle cell (by
          simpa only [FlatMemoThunk.lookupOrInsert, found, Cache.put, ite_eq_right same] using stored)

/-- A phase update retains the original stored request and its admission. -/
theorem Requests.status (property : Request → Prop) (handle : Nat) (phase : FlatMemoThunk.Status Answer)
    (state : FlatMemoThunk.State Key Request Answer) (covered : Requests property state) :
    Requests property (FlatMemoThunk.setStatus handle phase state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.setStatus, found] using covered
  | some original =>
      intro other cell stored
      by_cases same : other = handle
      · subst other
        have equal : { original with status := phase } = cell := by
          simpa [FlatMemoThunk.setStatus, found, Cache.put] using stored
        subst cell
        exact covered handle original found
      · exact covered other cell (by
          simpa only [FlatMemoThunk.setStatus, found, Cache.put, ite_eq_right same] using stored)

/-- Actual demand starts or observes the same admitted request. -/
theorem Requests.demand (property : Request → Prop) (handle : Nat)
    (state : FlatMemoThunk.State Key Request Answer) (covered : Requests property state) :
    Requests property (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using covered
  | some cell =>
      cases cell with
      | mk request phase =>
          cases phase with
          | suspended => simpa only [FlatMemoThunk.demand, found] using Requests.status property handle .evaluating state covered
          | evaluating | returned value => simpa only [FlatMemoThunk.demand, found] using covered

/-- Actual finish retains the evaluating request independently of the candidate result. -/
theorem Requests.finish (property : Request → Prop) (handle : Nat) (value : Answer)
    (state : FlatMemoThunk.State Key Request Answer) (covered : Requests property state) :
    Requests property (FlatMemoThunk.finish handle value state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.finish, found] using covered
  | some cell =>
      cases cell with
      | mk request phase =>
          cases phase with
          | evaluating => simpa only [FlatMemoThunk.finish, found] using Requests.status property handle (.returned value) state covered
          | suspended | returned prior => simpa only [FlatMemoThunk.finish, found] using covered

/-- Node operands and every enclosing pair name belong to the fixed input inventory. -/
def NodeCovered (inputs : FiniteInput view) (request : NodeRequest Symbol Guard) : Prop :=
  NodeInputs view (finiteInputMeaning view inputs) request ∧ SeenCovered inputs request.domain.key

/-- Both ordered edge-child lists and enclosing pair names belong to the fixed inventory. -/
def EdgeCovered (inputs : FiniteInput view) (request : EdgeRequest Symbol Guard) : Prop :=
  EdgeInputs view (finiteInputMeaning view inputs) request ∧ SeenCovered inputs request.domain.key

/-- Request coverage applies to all cells, including suspended and running cells. -/
structure Covered (inputs : FiniteInput view) (state : Native width Symbol Guard) : Prop where
  nodes : Requests (NodeCovered inputs) state.nodes
  edges : Requests (EdgeCovered inputs) state.edges

/-- Empty native tables derive coverage without a result or request premise. -/
theorem initial_covered (inputs : FiniteInput view) (width : Nat) (machine : Machine Symbol Guard) :
    Covered inputs (initial width machine) := ⟨Requests.empty _, Requests.empty _⟩

/-- Machine effects do not change stored requests in either native table. -/
theorem advance_covered (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (after : Machine Symbol Guard) (covered : Covered inputs state) : Covered inputs (advance state after) :=
  ⟨covered.nodes, covered.edges⟩

/-- Node publication derives coverage before any evaluation of a new request. -/
theorem lookupNode_covered (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (request : NodeRequest Symbol Guard) (covered : Covered inputs state) (known : NodeCovered inputs request) :
    Covered inputs (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using covered
  | some keyValue =>
      simp only [lookupNode, key]
      exact ⟨Requests.lookup _ keyValue request state.nodes covered.nodes known, covered.edges⟩

/-- Edge publication retains both original ordered child lists. -/
theorem lookupEdge_covered (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (request : EdgeRequest Symbol Guard) (covered : Covered inputs state) (known : EdgeCovered inputs request) :
    Covered inputs (lookupEdge width request state).2 :=
  ⟨covered.nodes, Requests.lookup _ _ request state.edges covered.edges known⟩

/-- Node demand retains coverage through suspended, busy, ready, and absent observations. -/
theorem demandNode_covered (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (handle : Nat) (covered : Covered inputs state) : Covered inputs (demandNode handle state).2 :=
  ⟨Requests.demand _ handle state.nodes covered.nodes, covered.edges⟩

/-- Edge demand retains the same causal request admission. -/
theorem demandEdge_covered (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (handle : Nat) (covered : Covered inputs state) : Covered inputs (demandEdge handle state).2 :=
  ⟨covered.nodes, Requests.demand _ handle state.edges covered.edges⟩

/-- Node finish changes no original request and needs no supplied result-language law. -/
theorem finishNode_covered (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (handle : Nat) (result : Value Symbol Guard) (covered : Covered inputs state) :
    Covered inputs (finishNode handle result state) :=
  ⟨Requests.finish _ handle result state.nodes covered.nodes, covered.edges⟩

/-- Edge finish retains admission of its actual original row request. -/
theorem finishEdge_covered (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (handle : Nat) (result : EdgeValue Symbol Guard) (covered : Covered inputs state) :
    Covered inputs (finishEdge handle result state) :=
  ⟨covered.nodes, Requests.finish _ handle result state.edges covered.edges⟩

/-- All-phase coverage derives the weaker admission invariant on actual returned cells. -/
theorem Covered.admitted {inputs : FiniteInput view} {state : Native width Symbol Guard}
    (covered : Covered inputs state) :
    SourceCurrentAllocatedNativeInputModelTransport.Admitted view (finiteInputMeaning view inputs) state :=
  ⟨fun handle _request _result found => (covered.nodes handle _ found).1,
    fun handle _request _result found => (covered.edges handle _ found).1⟩

/-- The same actual returned cells retain covered names for every seen pair. -/
theorem Covered.seen_admitted {inputs : FiniteInput view} {state : Native width Symbol Guard}
    (covered : Covered inputs state) : SeenAdmitted inputs state :=
  ⟨fun handle _request _result found => (covered.nodes handle _ found).2,
    fun handle _request _result found => (covered.edges handle _ found).2⟩

/-- Checked physical keys identify the admitted original node request in any stored phase. -/
theorem node_published (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (covered : Covered inputs state) (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard))
    (stored : state.nodes.cells handle = some cell) : cell.request = request ∧ NodeCovered inputs request := by
  have same := SourceCurrentAllocatedNativePhysicalCache.node_request_exact state physical request ready key checked handle published cell stored
  exact ⟨same, same ▸ covered.nodes handle cell stored⟩

/-- Checked edge keys retain original row order and covered children in every stored phase. -/
theorem edge_published (inputs : FiniteInput view) (state : Native width Symbol Guard)
    (covered : Covered inputs state) (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : EdgeKeyOf width request key)
    (handle : Nat) (published : state.edges.table key = some handle)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard))
    (stored : state.edges.cells handle = some cell) : cell.request = request ∧ EdgeCovered inputs request := by
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_request_exact state physical request ready key checked handle published cell stored
  exact ⟨same, same ▸ covered.edges handle cell stored⟩

/-- Derived view agreement transports coverage of the same cells in every phase. -/
theorem Covered.rebase {oldView newView : View Symbol}
    {before : FiniteInput oldView} {after : FiniteInput newView}
    (agreement : SourceCurrentAllocatedNativeContextRebase.Agreement before after)
    {state : Native width Symbol Guard} (covered : Covered before state) : Covered after state := by
  constructor
  · intro handle cell stored
    have known := covered.nodes handle cell stored
    exact ⟨agreement.node_inputs known.1, agreement.seen_covered known.2⟩
  · intro handle cell stored
    have known := covered.edges handle cell stored
    exact ⟨agreement.edge_inputs known.1, agreement.seen_covered known.2⟩

end MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache
