import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCache
import MicroCFTA.SourceRecursiveIntersectionInputGrowth

/-!
# Original source origins of captured checked native requests

Each allocated phase retains its original operand scope and actual source
reads for the enclosing pairs. Numeric inventory membership does not imply
these reads. Lookup receives the actual new request origin. Demand and
finish preserve the captured request without a returned-result premise.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original OriginalInput)
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

/-- Each enclosing pair retains complete original records at both actual source reads. -/
def Seen (source : State Symbol Guard) (domain : DomainKey) : Prop :=
  ∀ pair ∈ domain.seen, ∃ left right, Original left ∧ Original right ∧
    SourcePreparedSharedRows.read source pair.1 = some left ∧
    SourcePreparedSharedRows.read source pair.2 = some right

/-- The literal empty domain has no captured pair-read obligation. -/
theorem empty_seen (source : State Symbol Guard) : Seen source IntersectionEmptyDomain.emptyDomain.key := by
  intro pair absent
  cases absent

/-- A captured node has complete original operands, original bindings, and actual enclosing pair reads. -/
structure NodeOrigin (source : State Symbol Guard) (request : NodeRequest Symbol Guard) : Prop where
  scope : NodeScope source request
  seen : Seen source request.domain.key

/-- A captured row retains both original resident rows and actual enclosing pair reads. -/
structure EdgeOrigin (source : State Symbol Guard) (request : EdgeRequest Symbol Guard) : Prop where
  scope : EdgeScope source request
  seen : Seen source request.domain.key

/-- All allocated cells retain their captured origin independently of their phase or returned value. -/
def Captured (origin : Request → Prop) (state : FlatMemoThunk.State Key Request Answer) : Prop :=
  ∀ handle cell, state.cells handle = some cell → origin cell.request

/-- Both native families retain their complete original request origins in every allocated phase. -/
structure Stored (source : State Symbol Guard) (state : Native width Symbol Guard) : Prop where
  nodes : Captured (NodeOrigin source) state.nodes
  edges : Captured (EdgeOrigin source) state.edges

/-- Old captured availability and new pure coverage recover the old node input condition. -/
theorem NodeOrigin.inputs_back {source later : State Symbol Guard} {request : NodeRequest Symbol Guard}
    (origin : NodeOrigin source request)
    (inputs : SourceCurrentConstrainedCapNativeOccurrenceCache.NodeInputs later request) :
    SourceCurrentConstrainedCapNativeOccurrenceCache.NodeInputs source request :=
  ⟨origin.scope.left, origin.scope.right, origin.scope.leftAvailable, origin.scope.rightAvailable,
    inputs.2.2.2.2.1, inputs.2.2.2.2.2⟩

/-- Old resident rows and new pure coverage recover every old ordered row-child input condition. -/
theorem EdgeOrigin.inputs_back {source later : State Symbol Guard} {request : EdgeRequest Symbol Guard}
    (facts : Facts source) (origin : EdgeOrigin source request)
    (inputs : SourceCurrentConstrainedCapNativeOccurrenceCache.EdgeInputs later request) :
    SourceCurrentConstrainedCapNativeOccurrenceCache.EdgeInputs source request := by
  constructor
  · intro value member
    exact ⟨origin.scope.left value member,
      facts.cached.edges _ _ origin.scope.leftResident value member, (inputs.1 value member).2.2⟩
  · intro value member
    exact ⟨origin.scope.right value member,
      facts.cached.edges _ _ origin.scope.rightResident value member, (inputs.2 value member).2.2⟩

/-- New annotated bindings identify the same original Mu witnesses in the captured source. -/
theorem bindings_back (annotation : Guard → Prop) (source later : State Symbol Guard)
    (growth : Grows source later) (history : Extends source.nodes.issued later.nodes.issued)
    (facts : Facts later) (domain : DomainKey) (originals : OriginalBindings source domain)
    (bindings : SourceCurrentConstrainedCapNativeOccurrenceCache.OriginalBindings annotation later domain) :
    SourceCurrentConstrainedCapNativeOccurrenceCache.OriginalBindings annotation source domain := by
  intro name member
  obtain ⟨old, original, available, encoded⟩ := originals name member
  obtain ⟨value, present, reference, annotated, covered, _original⟩ := bindings name member
  have oldRead := SourceRecursiveIntersectionInputView.payload_readback later facts old
    (available.grows source later growth history) (.mu name) encoded
  have newEncoded : IntersectionFlatMemoKey.input value.referenceOf = some (.mu name) := by rw [reference]; rfl
  have newRead := SourceRecursiveIntersectionInputView.payload_readback later facts value present (.mu name) newEncoded
  have same : old = value := oldRead.symm.trans newRead
  exact ⟨old, available, same ▸ reference, same ▸ annotated, same ▸ covered, original⟩

private theorem captured_empty (origin : Request → Prop) :
    Captured origin (FlatMemoThunk.empty : FlatMemoThunk.State Key Request Answer) := by
  intro handle cell absent
  cases absent

private theorem captured_lookup [DecidableEq Key] (origin : Request → Prop)
    (key : Key) (request : Request) (state : FlatMemoThunk.State Key Request Answer)
    (known : Captured origin state) (actual : origin request) :
    Captured origin (FlatMemoThunk.lookupOrInsert key request state).2 := by
  cases found : state.table key with
  | some handle => simpa only [FlatMemoThunk.lookupOrInsert, found] using known
  | none =>
      intro handle cell stored
      by_cases same : handle = state.next
      · subst handle
        have equal : (⟨request, .suspended⟩ : FlatMemoThunk.Cell Request Answer) = cell := by
          simpa [FlatMemoThunk.lookupOrInsert, found, Cache.put] using stored
        cases equal
        exact actual
      · exact known handle cell (by
          simpa only [FlatMemoThunk.lookupOrInsert, found, Cache.put, ite_eq_right same] using stored)

private theorem captured_status (origin : Request → Prop) (handle : Nat) (phase : FlatMemoThunk.Status Answer)
    (state : FlatMemoThunk.State Key Request Answer) (known : Captured origin state) :
    Captured origin (FlatMemoThunk.setStatus handle phase state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.setStatus, found] using known
  | some original =>
      intro other cell stored
      by_cases same : other = handle
      · subst other
        have equal : { original with status := phase } = cell := by
          simpa [FlatMemoThunk.setStatus, found, Cache.put] using stored
        cases equal
        exact known handle original found
      · exact known other cell (by
          simpa only [FlatMemoThunk.setStatus, found, Cache.put, ite_eq_right same] using stored)

private theorem captured_demand (origin : Request → Prop) (handle : Nat)
    (state : FlatMemoThunk.State Key Request Answer) (known : Captured origin state) :
    Captured origin (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using known
  | some cell =>
      cases cell with
      | mk request phase =>
          cases phase with
          | suspended => simpa only [FlatMemoThunk.demand, found] using captured_status origin handle .evaluating state known
          | evaluating | returned value => simpa only [FlatMemoThunk.demand, found] using known

private theorem captured_finish (origin : Request → Prop) (handle : Nat) (value : Answer)
    (state : FlatMemoThunk.State Key Request Answer) (known : Captured origin state) :
    Captured origin (FlatMemoThunk.finish handle value state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.finish, found] using known
  | some cell =>
      cases cell with
      | mk request phase =>
          cases phase with
          | suspended | returned previous => simpa only [FlatMemoThunk.finish, found] using known
          | evaluating => simpa only [FlatMemoThunk.finish, found] using captured_status origin handle (.returned value) state known

variable (source : State Symbol Guard)

/-- Empty native tables have no captured request to supply. -/
theorem initial_stored (width : Nat) (machine : Machine Symbol Guard) : Stored source (initial width machine) :=
  ⟨captured_empty _, captured_empty _⟩

/-- Machine advance does not change any captured request. -/
theorem advance_stored (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (origins : Stored source state) : Stored source (advance state after) := ⟨origins.nodes, origins.edges⟩

/-- Actual node publication records its supplied original scope and pair reads. -/
theorem lookupNode_stored (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (origins : Stored source state) (actual : NodeOrigin source request) :
    Stored source (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using origins
  | some value =>
      simp only [lookupNode, key]
      exact ⟨captured_lookup _ value request state.nodes origins.nodes actual, origins.edges⟩

/-- Actual row publication records its supplied original scope and pair reads. -/
theorem lookupEdge_stored (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (origins : Stored source state) (actual : EdgeOrigin source request) :
    Stored source (lookupEdge width request state).2 :=
  ⟨origins.nodes, captured_lookup _ _ request state.edges origins.edges actual⟩

/-- Node demand preserves the original request in every phase. -/
theorem demandNode_stored (state : Native width Symbol Guard) (handle : Nat) (origins : Stored source state) :
    Stored source (demandNode handle state).2 := ⟨captured_demand _ handle state.nodes origins.nodes, origins.edges⟩

/-- Row demand preserves the original request in every phase. -/
theorem demandEdge_stored (state : Native width Symbol Guard) (handle : Nat) (origins : Stored source state) :
    Stored source (demandEdge handle state).2 := ⟨origins.nodes, captured_demand _ handle state.edges origins.edges⟩

/-- Node finish preserves request origins without assuming a result law. -/
theorem finishNode_stored (state : Native width Symbol Guard) (handle : Nat) (value : Value Symbol Guard)
    (origins : Stored source state) : Stored source (finishNode handle value state) :=
  ⟨captured_finish _ handle value state.nodes origins.nodes, origins.edges⟩

/-- Row finish preserves request origins without assuming a result law. -/
theorem finishEdge_stored (state : Native width Symbol Guard) (handle : Nat) (value : EdgeValue Symbol Guard)
    (origins : Stored source state) : Stored source (finishEdge handle value state) :=
  ⟨origins.nodes, captured_finish _ handle value state.edges origins.edges⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointOrigins
