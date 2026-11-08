import MicroCFTA.SourceSynthesisProgramMemoRoles
import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceSynthesisNativeTypeTrace

/-!
# Type and recursive Program fields in the actual outer memo tables

Each returned cell relates its complete captured owner to its result.
Type and Program implications share the same tables. Mixed Program guards
need no Type annotation. Physical updates retain both result families.
Ready hits transfer certificates through exact physical owner equality.

Publication is a generic store law. Its premise must be proved for the
actual running body. These laws do not establish that premise, all reached
field preservation, worker completion or an original-input driver bound.
-/
namespace MicroCFTA.SourceSynthesisHereditaryMemoFields
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState (NodeRequest EdgeRequest)
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable {width : Nat} {lib : Library} {literal : String → Symbol}

/-- A complete Type row has an annotated guard and annotated children. -/
def TypeRow (lib : Library) (row : Edge) : Prop :=
  Origin lib row.entry.key.constraint ∧ ∀ child ∈ row.children, Annotated (Origin lib) child

/-- Each captured node retains both conditional Type and recursive Program fields. -/
structure NodeFields (lib : Library) (literal : String → Symbol) (request : NodeRequest) (result : Node) : Prop where
  typed : Annotated (Origin lib) request.value → Annotated (Origin lib) result
  program : ValueFields (Origin lib) literal request.value → ValueFields (Origin lib) literal result

/-- Each captured row retains its complete Type or recursive Program certificate. -/
structure EdgeFields (lib : Library) (literal : String → Symbol) (request : EdgeRequest) (result : Edge) : Prop where
  typed : TypeRow lib request.value → TypeRow lib result
  program : SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal request.value →
    SourceSynthesisHereditaryProgramFields.EdgeFields (Origin lib) literal result

/-- Both actual result families retain complete owner links and conditional fields. -/
structure History (lib : Library) (literal : String → Symbol) (before : Caller width) : Prop where
  nodes : FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (NodeFields lib literal)) before.nodeResults
  edges : FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (EdgeFields lib literal)) before.edgeResults

/-- Empty outer families require no supplied input or result fields. -/
theorem initial (lib : Library) (literal : String → Symbol) (checked : Checked width) (memo : Memo) (fourth : Fourth) :
    History lib literal (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Physical caller updates retain both immutable outer result families. -/
theorem advance {before : Caller width} (history : History lib literal before)
    (checked : Checked width) (fourth : Fourth) (memo : Memo) :
    History lib literal (SourceCurrentAllocatedPartialState.advance before checked fourth memo) :=
  ⟨history.nodes, history.edges⟩

/-- Actual node lookup and demand retain earlier returned certificates. -/
theorem beginNode {before : Caller width} (history : History lib literal before) (request : NodeRequest) :
    History lib literal (SourceCurrentAllocatedPartialState.beginNode request before).2.2 := by
  have inserted := FlatMemoThunk.lookup_valid request.key request before.nodeResults
    (fun request key => request.key = key) (FlatMemoThunk.CellSpec (NodeFields lib literal)) history.nodes rfl trivial
  exact ⟨FlatMemoThunk.demand_spec _ _ _ _ inserted, history.edges⟩

/-- Actual edge lookup and demand retain earlier returned certificates. -/
theorem beginEdge {before : Caller width} (history : History lib literal before) (request : EdgeRequest) :
    History lib literal (SourceCurrentAllocatedPartialState.beginEdge request before).2.2 := by
  have inserted := FlatMemoThunk.lookup_valid request.key request before.edgeResults
    (fun request key => request.key = key) (FlatMemoThunk.CellSpec (EdgeFields lib literal)) history.edges rfl trivial
  exact ⟨history.nodes, FlatMemoThunk.demand_spec _ _ _ _ inserted⟩

/-- Generic node publication requires fields for the actual evaluating owner. -/
theorem finishNode {before : Caller width} {handle : Nat} {owner : NodeRequest} {value : Node}
    (history : History lib literal before)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (published : NodeFields lib literal owner value) :
    History lib literal (SourceCurrentAllocatedPartialState.finishNode handle value before) := by
  refine ⟨FlatMemoThunk.finish_spec handle value before.nodeResults _ _ history.nodes ?_, history.edges⟩
  intro request found
  have same := congrArg (fun cell : FlatMemoThunk.Cell NodeRequest Node => cell.request)
    (Option.some.inj (running.symm.trans found))
  change owner = request at same
  subst request
  exact published

/-- Generic edge publication requires fields for the actual evaluating owner. -/
theorem finishEdge {before : Caller width} {handle : Nat} {owner : EdgeRequest} {value : Edge}
    (history : History lib literal before)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (published : EdgeFields lib literal owner value) :
    History lib literal (SourceCurrentAllocatedPartialState.finishEdge handle value before) := by
  refine ⟨history.nodes, FlatMemoThunk.finish_spec handle value before.edgeResults _ _ history.edges ?_⟩
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

/-- A ready node hit transfers both certificates through exact complete owner equality. -/
theorem node_ready {before after : Caller width} {request : NodeRequest} {handle : Nat} {result : Node}
    (history : History lib literal before) (good : Good before) (ready : NodeReady before request)
    (started : SourceCurrentAllocatedPartialState.beginNode request before = (handle, .ready result, after)) :
    after = before ∧ NodeFields lib literal request result := by
  obtain ⟨owner, published, returned⟩ := lookup_demand_ready request.key request before.nodeResults result
    (congrArg (fun output => output.2.1) started)
  have handles : (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1 = handle :=
    congrArg Prod.fst started
  rw [handles] at published returned
  have unchanged := congrArg (fun output => output.2.2)
    (started.symm.trans (SourceCurrentAllocatedPartialState.beginNode_ready
      request owner before handle result published returned))
  obtain ⟨cell, stored, linked⟩ := good.nodes.linked request.key handle published
  have same : cell = ⟨owner, .returned result⟩ := Option.some.inj (stored.symm.trans returned)
  subst cell
  have ownerReady := (good.nodes.checked handle _ returned).1
  have ownerEq := SourceCurrentOuterPrefixInvariants.same_key good ownerReady ready linked
  change owner = request at ownerEq
  have certificate : NodeFields lib literal owner result := history.nodes.checked handle _ returned
  rw [ownerEq] at certificate
  exact ⟨unchanged, certificate⟩

/-- A ready edge hit retains the inherited owner and both conditional row certificates. -/
theorem edge_ready {before after : Caller width} {request : EdgeRequest} {handle : Nat} {result : Edge}
    (history : History lib literal before) (good : Good before) (ready : EdgeReady before request)
    (started : SourceCurrentAllocatedPartialState.beginEdge request before = (handle, .ready result, after)) :
    after = before ∧ EdgeFields lib literal request result := by
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
  have certificate : EdgeFields lib literal owner result := history.edges.checked handle _ returned
  rw [ownerEq] at certificate
  exact ⟨unchanged, certificate⟩

end MicroCFTA.SourceSynthesisHereditaryMemoFields
