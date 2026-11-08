import MicroCFTA.SourceSynthesisProgramMemoRoles
import MicroCFTA.SourceSynthesisNativeTypeParentWorker

/-!
# Captured source fields in the actual outer edge table

Each returned cell relates its actual captured owner to its result.
Application and filter certificates retain the complete source guard,
input arity, closed children and mixed Type fields. Top singleton rows
retain their original annotation or the literal Empty child.
Node-table updates leave this edge certificate unchanged.
Publication is a generic store law. Its premise must be proved for the
actual completed body. These laws do not prove that premise, hereditary
Program fields, all-reached preservation, completion or a driver bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeEdgeFieldHistory
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState (NodeRequest EdgeRequest)
open SourceCurrentOuterPrefixInvariants (Good EdgeReady)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisNativeTypeParentWorker (MixedSlots Coupled)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable {width : Nat} {lib : Library}

/-- Captured source layouts imply the corresponding fields of the complete result. -/
structure EdgeFields (lib : Library) (request : EdgeRequest) (result : Edge) : Prop where
  application : ∀ (types function argument : Expression) (sourceName : String)
      (sourceChildren : List Expression),
    SourceSynthesisFirstOrderConstruction.application types function argument =
        .node [.mk sourceName request.value.entry.key.constraint sourceChildren] →
    request.value.children.length = sourceChildren.length →
    ClosedValues request.value.children →
    MixedSlots lib (fun index => index = 2 ∨ index = 3) request.value.children →
    Coupled request.value result ∧ ClosedValues result.children ∧
      MixedSlots lib (fun index => index = 2 ∨ index = 3) result.children
  filter : ∀ (candidates goal : Expression) (sourceName : String)
      (sourceChildren : List Expression),
    SourceSynthesisFirstOrderConstruction.ofType candidates goal =
        .node [.mk sourceName request.value.entry.key.constraint sourceChildren] →
    request.value.children.length = sourceChildren.length →
    ClosedValues request.value.children →
    MixedSlots lib (fun index => index = 1) request.value.children →
    Coupled request.value result ∧ ClosedValues result.children ∧
      MixedSlots lib (fun index => index = 1) result.children
  annotated : ∀ annotation : Node,
    request.value.entry.key.constraint = top → request.value.children = [annotation] →
    Annotated (Origin lib) annotation → annotation.free = [] →
    result.entry.key.symbol = request.value.entry.key.symbol ∧ result.entry.key.constraint = top ∧
      (result.children = [annotation] ∨ result.children = [.empty]) ∧
      ∀ child ∈ result.children, Annotated (Origin lib) child

/-- The actual edge family retains its owner links and conditional returned fields. -/
structure History (lib : Library) (before : Caller width) : Prop where
  edges : FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (EdgeFields lib)) before.edgeResults

/-- Empty edge tables require no supplied field certificate. -/
theorem initial (lib : Library) (checked : Checked width) (memo : Memo) (fourth : Fourth) :
    History lib (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨FlatMemoThunk.empty_valid _ _⟩

/-- Physical advancement leaves the complete edge table unchanged. -/
theorem advance {before : Caller width} (history : History lib before)
    (checked : Checked width) (fourth : Fourth) (memo : Memo) :
    History lib (SourceCurrentAllocatedPartialState.advance before checked fourth memo) :=
  ⟨history.edges⟩

/-- Actual node lookup and demand leave the edge history unchanged. -/
theorem beginNode {before : Caller width} (history : History lib before) (request : NodeRequest) :
    History lib (SourceCurrentAllocatedPartialState.beginNode request before).2.2 :=
  ⟨history.edges⟩

/-- Actual edge lookup and demand retain earlier returned field certificates. -/
theorem beginEdge {before : Caller width} (history : History lib before) (request : EdgeRequest) :
    History lib (SourceCurrentAllocatedPartialState.beginEdge request before).2.2 := by
  have inserted := FlatMemoThunk.lookup_valid request.key request before.edgeResults
    (fun request key => request.key = key) (FlatMemoThunk.CellSpec (EdgeFields lib)) history.edges rfl trivial
  exact ⟨FlatMemoThunk.demand_spec _ _ _ _ inserted⟩

/-- Actual node publication leaves the edge history unchanged. -/
theorem finishNode {before : Caller width} (history : History lib before) (handle : Nat) (value : Node) :
    History lib (SourceCurrentAllocatedPartialState.finishNode handle value before) :=
  ⟨history.edges⟩

/-- Generic publication requires the certificate for the actual evaluating owner. -/
theorem finishEdge {before : Caller width} {handle : Nat} {owner : EdgeRequest} {value : Edge}
    (history : History lib before)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (published : EdgeFields lib owner value) :
    History lib (SourceCurrentAllocatedPartialState.finishEdge handle value before) := by
  refine ⟨FlatMemoThunk.finish_spec handle value before.edgeResults _ _ history.edges ?_⟩
  intro request found
  have same := congrArg (fun cell : FlatMemoThunk.Cell EdgeRequest Edge => cell.request)
    (Option.some.inj (running.symm.trans found))
  change owner = request at same
  subst request
  exact published

private theorem lookup_demand_ready {Key Request Result : Type} [DecidableEq Key]
    (key : Key) (request : Request) (memo : FlatMemoThunk.State Key Request Result) (result : Result)
    (ready : (FlatMemoThunk.demand (FlatMemoThunk.lookupOrInsert key request memo).1
      (FlatMemoThunk.lookupOrInsert key request memo).2).1 = .ready result) :
    ∃ original, memo.table key = some (FlatMemoThunk.lookupOrInsert key request memo).1 ∧
      memo.cells (FlatMemoThunk.lookupOrInsert key request memo).1 = some ⟨original, .returned result⟩ := by
  cases found : memo.table key with
  | none => simp [FlatMemoThunk.lookupOrInsert, found, FlatMemoThunk.demand, Cache.put] at ready
  | some handle =>
      have observed : (FlatMemoThunk.demand handle memo).1 = .ready result := by
        simpa only [FlatMemoThunk.lookupOrInsert, found] using ready
      obtain ⟨original, returned, _same⟩ := FlatMemoThunk.demand_ready_original handle memo result
        (FlatMemoThunk.demand handle memo).2 (Prod.ext observed rfl)
      exact ⟨original, by simp only [FlatMemoThunk.lookupOrInsert, found],
        by simpa only [FlatMemoThunk.lookupOrInsert, found] using returned⟩

/-- A ready hit retains the complete caller and transfers fields by exact owner equality. -/
theorem edge_ready {before after : Caller width} {request : EdgeRequest} {handle : Nat} {result : Edge}
    (history : History lib before) (good : Good before) (ready : EdgeReady before request)
    (started : SourceCurrentAllocatedPartialState.beginEdge request before = (handle, .ready result, after)) :
    after = before ∧ EdgeFields lib request result := by
  obtain ⟨owner, published, returned⟩ := lookup_demand_ready request.key request before.edgeResults result
    (congrArg (fun output => output.2.1) started)
  have handles : (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).1 = handle :=
    congrArg Prod.fst started
  rw [handles] at published returned
  have unchanged := congrArg (fun output => output.2.2)
    (started.symm.trans (SourceCurrentAllocatedPartialState.beginEdge_ready
      request owner before handle result published returned))
  obtain ⟨cell, stored, linked⟩ := good.edges.linked request.key handle published
  have same : cell = ⟨owner, .returned result⟩ := Option.some.inj (stored.symm.trans returned)
  subst cell
  have ownerReady := (good.edges.checked handle _ returned).1
  have ownerEq := SourceSynthesisProgramMemoRoles.edge_same_key good ownerReady ready linked
  change owner = request at ownerEq
  have certificate : EdgeFields lib owner result := history.edges.checked handle _ returned
  rw [ownerEq] at certificate
  exact ⟨unchanged, certificate⟩

end MicroCFTA.SourceSynthesisNativeTypeEdgeFieldHistory
