import MicroCFTA.SourceEqualityNativeDemandMemo
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.InternedGuardedLanguage

/-!
# Completed checked native requests

Completed cells retain an actual checked body execution. Physical records
and the independent language law are separate parts of the receipt. The
language law applies to closed inputs in the empty domain. Other domains
retain execution provenance but need a separate open-context language law.
The eager kernel Produced predicates do not define these receipts.
-/
namespace MicroCFTA.SourceEqualityNativeDemandProvenance
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Closed native node results have the independent intersection language. -/
def NodeMeaning (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (value : Value Symbol Guard) : Prop :=
  request.domain = IntersectionEmptyDomain.emptyDomain → request.left.free = [] → request.right.free = [] →
    ∀ ambient term, InternedGuardedLanguage.meaning holds ambient value term ↔
      InternedGuardedLanguage.meaning holds ambient request.left term ∧
      InternedGuardedLanguage.meaning holds ambient request.right term

/-- Closed native edge results have the independent intersection language. -/
def EdgeMeaning (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (value : EdgeValue Symbol Guard) : Prop :=
  request.domain = IntersectionEmptyDomain.emptyDomain →
    MergedColdReaderClosedInputs.ClosedValues request.left.children →
    MergedColdReaderClosedInputs.ClosedValues request.right.children →
    ∀ ambient term, InternedGuardedLanguage.edgeMeaning holds ambient value term ↔
      InternedGuardedLanguage.edgeMeaning holds ambient request.left term ∧
      InternedGuardedLanguage.edgeMeaning holds ambient request.right term

/-- A node receipt records checked body execution and its exact physical and language results. -/
def NodeProduced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (machine : Machine Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ (before after : Checked width), ∃ fuel,
    NodeReady before.native.machine request ∧
    SourceEqualityNativeDemand.execute fuel (.code (compileNode request)) before = .done value after ∧
    Extension before.native.machine after.native.machine ∧
    Available after.native.machine.heap value ∧
    Extension after.native.machine machine ∧ NodeMeaning holds request value

/-- An edge receipt records the checked body, including its equality-operation state. -/
def EdgeProduced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (machine : Machine Symbol Guard)
    (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard) : Prop :=
  ∃ (before after : Checked width), ∃ fuel,
    EdgeReady before.native.machine request ∧
    SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) before = .done value after ∧
    Extension before.native.machine after.native.machine ∧
    EdgeResident after.native.machine.heap value ∧
    Extension after.native.machine machine ∧ EdgeMeaning holds request value

/-- Later physical and domain effects retain the same actual node execution receipt. -/
theorem NodeProduced.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {before after : Machine Symbol Guard}
    {request : NodeRequest Symbol Guard} {value : Value Symbol Guard}
    (produced : NodeProduced (width := width) holds before request value) (growth : Extension before after) :
    NodeProduced (width := width) holds after request value := by
  obtain ⟨first, final, fuel, ready, done, grew, available, later, meaning⟩ := produced
  exact ⟨first, final, fuel, ready, done, grew, available, later.trans growth, meaning⟩

/-- Later physical and domain effects retain the same actual edge execution receipt. -/
theorem EdgeProduced.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {before after : Machine Symbol Guard}
    {request : EdgeRequest Symbol Guard} {value : EdgeValue Symbol Guard}
    (produced : EdgeProduced (width := width) holds before request value) (growth : Extension before after) :
    EdgeProduced (width := width) holds after request value := by
  obtain ⟨first, final, fuel, ready, done, grew, resident, later, meaning⟩ := produced
  exact ⟨first, final, fuel, ready, done, grew, resident, later.trans growth, meaning⟩

/-- A node receipt derives current input and result availability and its language law. -/
theorem NodeProduced.spec [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {machine : Machine Symbol Guard}
    {request : NodeRequest Symbol Guard} {value : Value Symbol Guard}
    (produced : NodeProduced (width := width) holds machine request value) :
    NodeReady machine request ∧ Available machine.heap value ∧ NodeMeaning holds request value := by
  obtain ⟨first, final, fuel, ready, done, grew, available, later, meaning⟩ := produced
  have growth := grew.trans later
  exact ⟨⟨ready.1.grows _ growth, growth.available _ ready.2.1, growth.available _ ready.2.2⟩,
    later.available _ available, meaning⟩

/-- An edge receipt derives current complete resident inputs and result and its language law. -/
theorem EdgeProduced.spec [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {machine : Machine Symbol Guard}
    {request : EdgeRequest Symbol Guard} {value : EdgeValue Symbol Guard}
    (produced : EdgeProduced (width := width) holds machine request value) :
    EdgeReady machine request ∧ EdgeResident machine.heap value ∧ EdgeMeaning holds request value := by
  obtain ⟨first, final, fuel, ready, done, grew, resident, later, meaning⟩ := produced
  have growth := grew.trans later
  exact ⟨⟨ready.1.grows _ growth, edge_grows _ _ growth.heap _ ready.2.1,
    edge_grows _ _ growth.heap _ ready.2.2⟩, edge_grows _ _ later.heap _ resident, meaning⟩

/-- Every node phase retains its original inputs; a returned phase has checked provenance. -/
def NodeGood [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (machine : Machine Symbol Guard)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard)) : Prop :=
  NodeReady machine cell.request ∧ match cell.status with
    | .returned value => NodeProduced (width := width) holds machine cell.request value
    | _ => True

/-- Every edge phase retains its complete original rows; a returned phase has checked provenance. -/
def EdgeGood [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (machine : Machine Symbol Guard)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)) : Prop :=
  EdgeReady machine cell.request ∧ match cell.status with
    | .returned value => EdgeProduced (width := width) holds machine cell.request value
    | _ => True

/-- Checked native validity retains actual source word bounds and both completed-cell receipts. -/
structure Valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (state : Native width Symbol Guard) : Prop where
  machine : SourceRecursiveIntersectionKernel.Valid state.machine
  nodes : FlatMemoThunk.Valid (NodeKey width) (NodeGood (width := width) holds state.machine) state.nodes
  edges : FlatMemoThunk.Valid (EdgeKeyOf width) (EdgeGood (width := width) holds state.machine) state.edges

/-- Empty native tables have no completed-result assumption. -/
theorem initial_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) :
    Valid holds (initial width machine) := ⟨valid, FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Checked native validity implies structural memo validity. -/
theorem Valid.shape [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {holds : Guard → Term Symbol → Bool} {state : Native width Symbol Guard} (valid : Valid holds state) :
    SourceRecursiveIntersectionNative.Shape state := by
  constructor
  · exact ⟨valid.nodes.bounded, fun key handle stored => by
      obtain ⟨cell, present, linked⟩ := valid.nodes.linked key handle stored
      exact ⟨cell, present, linked.1⟩, fun _ _ _ => trivial⟩
  · exact ⟨valid.edges.bounded, fun key handle stored => by
      obtain ⟨cell, present, linked⟩ := valid.edges.linked key handle stored
      exact ⟨cell, present, linked.1⟩, fun _ _ _ => trivial⟩

end MicroCFTA.SourceEqualityNativeDemandProvenance
