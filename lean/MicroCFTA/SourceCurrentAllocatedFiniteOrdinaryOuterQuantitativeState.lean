import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned

/-!
# Complete lower stores and quantitative outer returned profiles

The state retains every earlier structural and lower guard certificate.
Each outer finish installs its derived quantitative owner law.
Warm hits recover the complete stored owner before profile transport.
These lifecycle laws do not prove a node or edge producer execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialMemoSound (Sound)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate EdgeCertificate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {width : Nat}

/-- The same state retains complete earlier stores and quantitative outer owner laws. -/
structure Stored (state : Caller width) : Prop where
  base : SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores.Stored state
  returned : SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned.Stored state

/-- The complete structural outer invariant follows from the retained earlier store. -/
theorem Stored.structural {state : Caller width} (stored : Stored state) :
    SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored state := stored.base.structural

/-- Fresh outer tables derive their quantitative laws over the supplied lower stores. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (native : NativeStored checked.native) (output : OutputStored checked.native) (profiles : Profiles memo)
    (guards : NativeGuards checked.native) (mergeGuards : MergeGuards memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores.initial checked memo fourth native output profiles guards mergeGuards,
    SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned.initial checked memo fourth⟩

/-- Literal root initialization derives quantitative certificates from empty outer tables. -/
theorem caller_stored (width : Nat) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (heap : InternedConstructorTemplates.State Symbol Guard) :
    Stored (SourceCurrentAllocatedPartialInitialization.caller width cache heap) :=
  ⟨SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores.caller_stored width cache heap,
    SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned.initial _ _ _⟩

/-- An actual lower return replaces its derived lower stores and retains complete outer tables. -/
theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (native : NativeStored checked.native)
    (output : OutputStored checked.native) (profiles : Profiles memo)
    (guards : NativeGuards checked.native) (mergeGuards : MergeGuards memo) :
    Stored (SourceCurrentAllocatedPartialState.advance before checked fourth memo) :=
  ⟨⟨stored.base.base.advance checked fourth memo native output profiles, guards, mergeGuards⟩,
    stored.returned.advance checked fourth memo⟩

/-- Physical advancement retains all result tables and their certificates. -/
theorem Stored.advancePhysical {before : Caller width} (stored : Stored before)
    (physical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula) :
    Stored (SourceCurrentAllocatedPartialState.advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked physical)
      before.fourth before.merge) :=
  ⟨⟨stored.base.base.advancePhysical physical,
      SourceCurrentAllocatedFiniteOrdinaryGuardStored.advance_stored _ _ stored.base.nativeGuard, stored.base.mergeGuard⟩,
    stored.returned.advance _ _ _⟩

/-- Node publication and demand add no returned result law. -/
theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (beginNode request before).2.2 :=
  ⟨⟨stored.base.base.beginNode request, stored.base.nativeGuard, stored.base.mergeGuard⟩,
    stored.returned.beginNode request⟩

/-- Edge publication and demand retain each earlier returned law. -/
theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (beginEdge request before).2.2 :=
  ⟨⟨stored.base.base.beginEdge request, stored.base.nativeGuard, stored.base.mergeGuard⟩,
    stored.returned.beginEdge request⟩

/-- Node finish installs both laws at the same exact evaluating owner. -/
theorem Stored.finishNode {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : NodeRequest} (result : Node)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DNode owner.value → NodeNarrow owner.value result)
    (quantitative : NodeCertificate owner result) : Stored (finishNode handle result before) :=
  ⟨⟨stored.base.base.finishNode result running law, stored.base.nativeGuard, stored.base.mergeGuard⟩,
    stored.returned.finishNode result running quantitative⟩

/-- Edge finish installs the parent profile before descendant traversal. -/
theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DEdge owner.value → EdgeNarrow owner.value result)
    (quantitative : EdgeCertificate owner result) : Stored (finishEdge handle result before) :=
  ⟨⟨stored.base.base.finishEdge result running law, stored.base.nativeGuard, stored.base.mergeGuard⟩,
    stored.returned.finishEdge result running quantitative⟩

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

/-- A ready node reads its complete captured owner and universal quantitative law. -/
theorem Stored.node_ready {before : Caller width} (stored : Stored before)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : NodeRequest) (after : Caller width) (handle : Nat) (result : Node)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap candidate.value)
    (started : SourceCurrentAllocatedPartialState.beginNode candidate before = (handle, .ready result, after)) :
    after = before ∧ NodeCertificate candidate result := by
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
  exact ⟨unchanged, stored.returned.node_hit coherent returned good.input available linked.2⟩

/-- A ready edge derives the requested quantitative law from its coherent stored owner. -/
theorem Stored.edge_ready {before : Caller width} (stored : Stored before)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : EdgeRequest) (after : Caller width) (handle : Nat) (result : Edge)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap candidate.value)
    (started : SourceCurrentAllocatedPartialState.beginEdge candidate before = (handle, .ready result, after)) :
    after = before ∧ EdgeCertificate candidate result := by
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
  exact ⟨unchanged, stored.returned.edge_hit coherent returned good.input resident linked.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState
