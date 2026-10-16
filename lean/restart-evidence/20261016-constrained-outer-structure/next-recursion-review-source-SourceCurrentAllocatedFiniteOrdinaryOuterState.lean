import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReturned
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCache
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
import MicroCFTA.SourceCurrentAllocatedPartialGraph

/-!
# Causal finite ordinary certificates in the current outer state

Native cells, merge entries, and outer cells retain separate certificates.
Publication creates no completed result. Each finish requires a local law
for its literal evaluating owner. Physical validity and language laws remain
separate. These lifecycle results do not assert caller completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialMemoSound (Sound)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "ReturnedStored" => SourceCurrentAllocatedFiniteOrdinaryReturned.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {width : Nat}

/-- The three distinct completed result families retain their captured structural laws. -/
structure Stored (state : Caller width) : Prop where
  native : NativeStored state.checked.native
  merge : MergeStored state.merge
  returned : ReturnedStored state

/-- Fresh outer tables retain the explicitly supplied lower warm certificates. -/
theorem initial (checked : Checked width) (memo : Memo) (fourth : Fourth)
    (native : NativeStored checked.native) (merged : MergeStored memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨native, merged, SourceCurrentAllocatedFiniteOrdinaryReturned.initial checked memo fourth⟩

/-- Actual lower returns replace their own certificates and retain the complete outer tables. -/
theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : Checked width) (fourth : Fourth) (memo : Memo)
    (native : NativeStored checked.native) (merged : MergeStored memo) :
    Stored (SourceCurrentAllocatedPartialState.advance before checked fourth memo) :=
  ⟨native, merged, stored.returned.advance checked fourth memo⟩

/-- Constructor-only physical advancement retains every structural certificate. -/
theorem Stored.advancePhysical {before : Caller width} (stored : Stored before)
    (physical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula) :
    Stored (SourceCurrentAllocatedPartialState.advance before
      (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked physical) before.fourth before.merge) :=
  stored.advance _ _ _ (SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ stored.native) stored.merge

/-- Node lookup, publication, and demand retain the three completed-result certificates. -/
theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (SourceCurrentAllocatedPartialState.beginNode request before).2.2 :=
  ⟨stored.native, stored.merge, stored.returned.beginNode request⟩

/-- Edge lookup, publication, and demand retain both outer families independently. -/
theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (SourceCurrentAllocatedPartialState.beginEdge request before).2.2 :=
  ⟨stored.native, stored.merge, stored.returned.beginEdge request⟩

/-- Node completion installs only the derived law of its actual evaluating owner. -/
theorem Stored.finishNode {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : NodeRequest} (result : Node)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DNode owner.value → NodeNarrow owner.value result) :
    Stored (SourceCurrentAllocatedPartialState.finishNode handle result before) :=
  ⟨stored.native, stored.merge, stored.returned.finishNode result running law⟩

/-- Edge completion installs only the derived law of its actual evaluating owner. -/
theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DEdge owner.value → EdgeNarrow owner.value result) :
    Stored (SourceCurrentAllocatedPartialState.finishEdge handle result before) :=
  ⟨stored.native, stored.merge, stored.returned.finishEdge result running law⟩

/-- Literal indexed descent changes no table that carries a structural result certificate. -/
theorem Stored.descend {before : Caller width} (stored : Stored before) (combined : EqValue) (index : Nat) :
    Stored (SourceCurrentAllocatedPartialGraph.descend before combined index).2 :=
  stored.advancePhysical _

/-- The actual inherited-first prefix retains all three completed-result families. -/
theorem Stored.prefixState {before : Caller width} (stored : Stored before) (edge : Edge) (inherited : EqValue) :
    Stored (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited) :=
  stored.advancePhysical _

/-- A literal node start transfers the requested domain to its complete captured owner. -/
theorem node_evaluate
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate owner : NodeRequest) (before running : Caller width) (handle : Nat)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints candidate.inherited)
    (available : Available before.checked.native.machine.heap candidate.value) (domain : DNode candidate.value)
    (started : SourceCurrentAllocatedPartialState.beginNode candidate before = (handle, .evaluate owner, running)) :
    owner.value = candidate.value ∧ DNode owner.value ∧ owner.key = candidate.key := by
  have current := SourceCurrentAllocatedPartialMemoSound.beginNode_evaluate_sound formulas solver candidate before
    sound inherited available handle owner running started
  have checked : running.checked = before.checked := by
    simpa only [started] using (beginNode_components candidate before).1
  have ownerAvailable : Available before.checked.native.machine.heap owner.value := by
    simpa only [checked] using current.2.2.1.input
  have same := SourceEqualityPartialKeyTransport.available_reference_eq _ coherent owner.value candidate.value
    ownerAvailable available (congrArg Prod.snd current.2.2.2)
  exact ⟨same, same.symm ▸ domain, current.2.2.2⟩

/-- A literal edge start transfers unrestricted full-guard domain through its actual owner key. -/
theorem edge_evaluate
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate owner : EdgeRequest) (before running : Caller width) (handle : Nat)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints candidate.inherited)
    (resident : EdgeResident before.checked.native.machine.heap candidate.value) (domain : DEdge candidate.value)
    (started : SourceCurrentAllocatedPartialState.beginEdge candidate before = (handle, .evaluate owner, running)) :
    owner.value = candidate.value ∧ DEdge owner.value ∧ owner.key = candidate.key := by
  have current := SourceCurrentAllocatedPartialMemoSound.beginEdge_evaluate_sound formulas solver candidate before
    sound inherited resident handle owner running started
  have checked : running.checked = before.checked := by
    simpa only [started] using (beginEdge_components candidate before).1
  have ownerResident : EdgeResident before.checked.native.machine.heap owner.value := by
    simpa only [checked] using current.2.2.1.input
  have same := edge_identity_unique _ coherent owner.value candidate.value ownerResident resident
    (congrArg Prod.snd current.2.2.2)
  exact ⟨same, same.symm ▸ domain, current.2.2.2⟩

private theorem lookup_demand_ready [DecidableEq Key] (key : Key) (request : Request)
    (memo : FlatMemoThunk.State Key Request Result) (result : Result)
    (ready : (FlatMemoThunk.demand (FlatMemoThunk.lookupOrInsert key request memo).1
      (FlatMemoThunk.lookupOrInsert key request memo).2).1 = .ready result) :
    ∃ owner, memo.table key = some (FlatMemoThunk.lookupOrInsert key request memo).1 ∧
      memo.cells (FlatMemoThunk.lookupOrInsert key request memo).1 = some ⟨owner, .returned result⟩ := by
  cases found : memo.table key with
  | none => simp [FlatMemoThunk.lookupOrInsert, found, FlatMemoThunk.demand, put] at ready
  | some handle =>
      have observed : (FlatMemoThunk.demand handle memo).1 = .ready result := by
        simpa only [FlatMemoThunk.lookupOrInsert, found] using ready
      obtain ⟨owner, returned, _⟩ := FlatMemoThunk.demand_ready_original handle memo result
        (FlatMemoThunk.demand handle memo).2 (Prod.ext observed rfl)
      exact ⟨owner, by simp only [FlatMemoThunk.lookupOrInsert, found],
        by simpa only [FlatMemoThunk.lookupOrInsert, found] using returned⟩

/-- An actual ready node observation derives narrowing from its own first stored owner. -/
theorem Stored.node_ready {before : Caller width} (stored : Stored before)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : NodeRequest) (after : Caller width) (handle : Nat) (result : Node)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap candidate.value) (domain : DNode candidate.value)
    (started : SourceCurrentAllocatedPartialState.beginNode candidate before = (handle, .ready result, after)) :
    after = before ∧ NodeNarrow candidate.value result := by
  obtain ⟨owner, published, returned⟩ := lookup_demand_ready candidate.key candidate before.nodeResults result
    (congrArg (fun result => result.2.1) started)
  have handles : (FlatMemoThunk.lookupOrInsert candidate.key candidate before.nodeResults).1 = handle := congrArg Prod.fst started
  rw [handles] at published returned
  have unchanged := congrArg (fun result => result.2.2)
    (started.symm.trans (beginNode_ready candidate owner before handle result published returned))
  have good := sound.nodes handle _ returned
  obtain ⟨cell, present, linked⟩ := sound.valid.nodes.linked candidate.key handle published
  have sameCell := Option.some.inj (present.symm.trans returned)
  subst cell
  exact ⟨unchanged, stored.returned.node_hit coherent returned good.input available linked.2 domain⟩

/-- An actual ready edge observation derives its bound without an owner-domain oracle. -/
theorem Stored.edge_ready {before : Caller width} (stored : Stored before)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : EdgeRequest) (after : Caller width) (handle : Nat) (result : Edge)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap candidate.value) (domain : DEdge candidate.value)
    (started : SourceCurrentAllocatedPartialState.beginEdge candidate before = (handle, .ready result, after)) :
    after = before ∧ EdgeNarrow candidate.value result := by
  obtain ⟨owner, published, returned⟩ := lookup_demand_ready candidate.key candidate before.edgeResults result
    (congrArg (fun result => result.2.1) started)
  have handles : (FlatMemoThunk.lookupOrInsert candidate.key candidate before.edgeResults).1 = handle := congrArg Prod.fst started
  rw [handles] at published returned
  have unchanged := congrArg (fun result => result.2.2)
    (started.symm.trans (beginEdge_ready candidate owner before handle result published returned))
  have good := sound.edges handle _ returned
  obtain ⟨cell, present, linked⟩ := sound.valid.edges.linked candidate.key handle published
  have sameCell := Option.some.inj (present.symm.trans returned)
  subst cell
  exact ⟨unchanged, stored.returned.edge_hit coherent returned good.input resident linked.2 domain⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
