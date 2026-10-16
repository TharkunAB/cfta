import MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain

/-!
# Current caller inputs from equality-free regions

Literal physical empty readback determines the effective source accessor.
Actual memo starts retain their stored owners. Initial resident key facts
identify each owner's complete value with the candidate value. Returned
edge shapes come from the actual stored cell, not a future body result.
Only the pure Region predicate is reused from the earlier caller model.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialPlainInputs
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Region" => SourceEqualityPartialPlainRegion.Region
local notation "Rows" => SourceEqualityPartialPlainRegion.Rows
local notation "Children" => SourceEqualityPartialPlainRegion.Children
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Sound" => SourceCurrentAllocatedPartialMemoSound.Sound

/-- Empty physical own readback requires an empty effective source equality list. -/
theorem own_empty (original : Guard)
    (physical : SourceEqualityPhysicalPayload.own original = .ok (some [])) :
    SourceCompactGuards.sourceEqualities original = some [] := by
  cases source : SourceCompactGuards.sourceEqualities original with
  | none => simp [SourceEqualityPhysicalPayload.own, source, SourceEqualityPhysicalPayload.read] at physical
  | some classes =>
      cases classes with
      | nil => rfl
      | cons first rest =>
          cases head : SourceEqualityClassOrder.recordOf first <;>
            cases tail : SourceEqualityClassOrder.recordsOf rest <;>
              simp [SourceEqualityPhysicalPayload.own, source, SourceEqualityPhysicalPayload.read,
                SourceEqualityClassOrder.recordsOf, head, tail] at physical

/-- Each literal child position retains its Region. -/
theorem children_member {values : List Node} (regions : Children values)
    (value : Node) (member : value ∈ values) : Region value := by
  cases regions with
  | nil => cases member
  | cons first rest =>
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ first
      · exact children_member rest value later
termination_by values.length

/-- Each original row has empty effective own equalities and its literal child Regions. -/
theorem rows_member {edges : List Edge} (rows : Rows edges) (edge : Edge) (member : edge ∈ edges) :
    SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some [] ∧ Children edge.children := by
  cases rows with
  | nil => cases member
  | cons physical children rest =>
      rcases List.mem_cons.mp member with same | later
      · subst edge
        exact ⟨own_empty _ physical, children⟩
      · exact rows_member rest edge later
termination_by edges.length

variable {width : Nat}

/-- An actual node start transfers the candidate Region to its exact resident owner value. -/
theorem node_evaluate
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate owner : NodeRequest) (before running : Caller width) (handle : Nat)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints candidate.inherited)
    (available : Available before.checked.native.machine.heap candidate.value)
    (region : Region candidate.value)
    (started : beginNode candidate before = (handle, .evaluate owner, running)) :
    owner.value = candidate.value ∧ Region owner.value := by
  have current := SourceCurrentAllocatedPartialMemoSound.beginNode_evaluate_sound formulas solver candidate before
    sound inheritedReady available handle owner running started
  have checked : running.checked = before.checked := by
    simpa only [started] using (beginNode_components candidate before).1
  have ownerAvailable : Available before.checked.native.machine.heap owner.value := by
    simpa only [checked] using current.2.2.1.input
  have values := SourceEqualityPartialKeyTransport.available_reference_eq _ coherent _ _ ownerAvailable available
    (congrArg Prod.snd current.2.2.2)
  exact ⟨values, values.symm ▸ region⟩

/-- An actual edge start transfers the original row facts to its complete resident owner. -/
theorem edge_evaluate
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate owner : EdgeRequest) (before running : Caller width) (handle : Nat)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints candidate.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap candidate.value)
    (plain : SourceCompactGuards.sourceEqualities candidate.value.entry.key.constraint = some [])
    (regions : Children candidate.value.children)
    (started : beginEdge candidate before = (handle, .evaluate owner, running)) :
    owner.value = candidate.value ∧
      SourceCompactGuards.sourceEqualities owner.value.entry.key.constraint = some [] ∧ Children owner.value.children := by
  have current := SourceCurrentAllocatedPartialMemoSound.beginEdge_evaluate_sound formulas solver candidate before
    sound inheritedReady resident handle owner running started
  have checked : running.checked = before.checked := by
    simpa only [started] using (beginEdge_components candidate before).1
  have ownerResident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap owner.value := by
    simpa only [checked] using current.2.2.1.input
  have values := InternedEdgeResidency.edge_identity_unique _ coherent _ _ ownerResident resident
    (congrArg Prod.snd current.2.2.2)
  exact ⟨values, by simpa only [values] using plain, by simpa only [values] using regions⟩

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

/-- A literal ready hit reuses its stored owner's concrete shape at the candidate value. -/
theorem edge_ready_shape
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (candidate : EdgeRequest) (before after : Caller width) (handle : Nat) (result : Edge)
    (sound : Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap candidate.value)
    (domain : SourceCurrentAllocatedPartialReturnedDomain.Stored before)
    (started : beginEdge candidate before = (handle, .ready result, after)) :
    after = before ∧ SourceCurrentAllocatedPartialReturnedDomain.Shape candidate.value result := by
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
  exact ⟨unchanged, values ▸ domain handle owner result returned⟩

end MicroCFTA.SourceCurrentAllocatedPartialPlainInputs
