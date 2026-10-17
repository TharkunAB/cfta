import MicroCFTA.SourceCurrentAllocatedPartialPlainInputs

/-!
# Conditional plain-owner certificates in mixed outer caches

Only an actual stored owner with empty effective own equalities has a
three-way child-shape obligation. Other completed constrained parents are
unrestricted. A warm hit reads the complete owner before using its law.
This module proves lifecycle and readback laws, not general progress.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalDomain
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State

/-- Empty own equalities use the full source accessor, including positive guard extraction. -/
def OwnEmpty (edge : Edge) : Prop :=
  SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some []

/-- Each returned plain owner retains its shape; unrelated completed parents remain unrestricted. -/
def Stored (state : Caller width) : Prop :=
  ∀ handle owner result, state.edgeResults.cells handle = some ⟨owner, .returned result⟩ →
    OwnEmpty owner.value → Shape owner.value result

/-- The earlier unconditional certificate implies the conditional certificate. -/
theorem Stored.of_unconditional {state : Caller width}
    (stored : SourceCurrentAllocatedPartialReturnedDomain.Stored state) : Stored state :=
  fun handle owner result returned _ => stored handle owner result returned

/-- Fresh outer tables impose no returned-law premise on lower warm state. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked merge fourth) := by
  intro handle owner result absent
  cases absent

/-- Lower execution retains the exact outer returned cells. -/
theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) :
    Stored (SourceCurrentAllocatedPartialState.advance before checked fourth merge) := stored

/-- Node publication changes no edge result cell. -/
theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (beginNode request before).2.2 := stored

/-- Node completion changes no edge result cell. -/
theorem Stored.finishNode {before : Caller width} (stored : Stored before) (handle : Nat) (result : Node) :
    Stored (finishNode handle result before) := stored

private theorem lookup_returned_before [DecidableEq Key] (key : Key) (request : Request)
    (memo : FlatMemoThunk.State Key Request Result) :
    FlatMemoThunk.Returned (FlatMemoThunk.lookupOrInsert key request memo).2 memo := by
  intro handle owner result returned
  cases found : memo.table key with
  | some existing => simpa only [FlatMemoThunk.lookupOrInsert, found] using returned
  | none =>
      by_cases same : handle = memo.next
      · subst handle
        simp [FlatMemoThunk.lookupOrInsert, found, put] at returned
      · simpa only [FlatMemoThunk.lookupOrInsert, found, put, ite_eq_right same] using returned

private theorem demand_returned_before (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    FlatMemoThunk.Returned (FlatMemoThunk.demand handle memo).2 memo := by
  intro other owner result returned
  cases found : memo.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using returned
  | some cell =>
      cases cell with
      | mk original status =>
          cases status with
          | evaluating | returned value => simpa only [FlatMemoThunk.demand, found] using returned
          | suspended =>
              by_cases same : other = handle
              · subst other
                simp [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus, put] at returned
              · simpa only [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus, put, ite_eq_right same] using returned

/-- Edge publication and demand add no returned law. -/
theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (beginEdge request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  intro handle owner result returned
  exact stored handle owner result
    (lookup_returned_before request.key request before.edgeResults handle owner result
      (demand_returned_before published.1 published.2 handle owner result returned))

/-- Finishing the exact evaluating owner requires only its conditional produced law. -/
theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (shape : OwnEmpty owner.value → Shape owner.value result) :
    Stored (finishEdge handle result before) := by
  intro other original output returned
  by_cases same : other = handle
  · subst other
    have installed := finishEdge_returned handle owner result before running
    have equal := Option.some.inj (installed.symm.trans returned)
    cases equal
    exact shape
  · exact stored other original output (by
      change (FlatMemoThunk.finish handle result before.edgeResults).cells other = _ at returned
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, put, ite_eq_right same] using returned)

private theorem ready_owner {Key Request Result : Type} [DecidableEq Key]
    (key : Key) (request : Request) (memo : FlatMemoThunk.State Key Request Result) (result : Result)
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

/-- Actual warm readback identifies the complete empty-own owner and unchanged caller state. -/
theorem edge_ready_owner
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : EdgeRequest) (before after : Caller width) (handle : Nat) (result : Edge)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap candidate.value)
    (emptyOwn : OwnEmpty candidate.value)
    (started : beginEdge candidate before = (handle, .ready result, after)) :
    ∃ owner, before.edgeResults.cells handle = some ⟨owner, .returned result⟩ ∧
      owner.value = candidate.value ∧ OwnEmpty owner.value ∧ after = before := by
  obtain ⟨owner, published, returned⟩ := ready_owner candidate.key candidate before.edgeResults result
    (congrArg (fun result => result.2.1) started)
  have handles : (FlatMemoThunk.lookupOrInsert candidate.key candidate before.edgeResults).1 = handle :=
    congrArg Prod.fst started
  rw [handles] at published returned
  have unchanged := congrArg (fun result => result.2.2)
    (started.symm.trans (beginEdge_ready candidate owner before handle result published returned))
  obtain ⟨cell, stored, linked⟩ := sound.valid.edges.linked candidate.key handle published
  have cells := Option.some.inj (stored.symm.trans returned)
  subst cell
  have values := InternedEdgeResidency.edge_identity_unique _ coherent _ _
    (sound.edges handle _ returned).input resident (congrArg Prod.snd linked.2)
  exact ⟨owner, returned, values, values.symm ▸ emptyOwn, unchanged⟩

/-- A queried empty-own edge uses only its actual stored owner's conditional shape. -/
theorem edge_ready_shape
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : EdgeRequest) (before after : Caller width) (handle : Nat) (result : Edge)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap candidate.value)
    (emptyOwn : OwnEmpty candidate.value) (domain : Stored before)
    (started : beginEdge candidate before = (handle, .ready result, after)) :
    after = before ∧ Shape candidate.value result := by
  obtain ⟨owner, returned, values, own, unchanged⟩ :=
    edge_ready_owner formulas solver candidate before after handle result sound coherent resident emptyOwn started
  exact ⟨unchanged, values ▸ domain handle owner result returned own⟩

/-- Conditional shape gives each actual returned child its Region and strict owner-relative rank. -/
theorem Stored.child {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} {result : Edge}
    (returned : before.edgeResults.cells handle = some ⟨owner, .returned result⟩) (own : OwnEmpty owner.value)
    (regions : SourceEqualityPartialPlainRegion.Children owner.value.children)
    (inherited : SourceEqualityConstraintAllocation.Value) (child : Node) (member : child ∈ result.children) :
    SourceEqualityPartialPlainRegion.Region child ∧
      SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨inherited, child⟩ <
        SourceCurrentAllocatedPartialActiveOrder.edgeRank owner := by
  have shape := stored handle owner result returned own
  have childBound := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge owner.inherited inherited result child member
  have bound := shape.height
  refine ⟨shape.child_region regions child member, ?_⟩
  simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank] at childBound ⊢
  omega

end MicroCFTA.SourceCurrentAllocatedPartialConditionalDomain
