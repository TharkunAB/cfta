import MicroCFTA.SourceCurrentAllocatedPartialEdgeActual

#print axioms MicroCFTA.SourceCurrentAllocatedPartialEdgeActual.edge_body
#check @MicroCFTA.SourceCurrentAllocatedPartialEdgeActual.edge_body
#print axioms MicroCFTA.SourceCurrentAllocatedPartialEdgeActual.edge_call
#check @MicroCFTA.SourceCurrentAllocatedPartialEdgeActual.edge_call

namespace MicroCFTA.PartialEdgeActualIndependent
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialMemoSound (Sound)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- The supplied evaluated body finishes the same original owner at its actual return. -/
theorem same_owner
    (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {request original : EdgeRequest} {before running middle : Caller width}
    {handle : Nat} {result : Edge} {memos final : Memos}
    (started : beginEdge request before = (handle, .evaluate original, running))
    {body : EdgeBody budget original running result middle}
    (reads : SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads F S body memos final)
    (ready : Ready before.checked) (admitted : At F S inventory before.checked)
    (sound : Sound F S before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct F S before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds F S) ambient before.merge)
    (ranges : SourceCurrentAllocatedPartialEdgeActual.CallRanges budget request before)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ next,
      SourceCurrentAllocatedPartialEdgeCall.Receipt F S next request before result
        (finishEdge handle result middle) final ∧
      ProbeHeap (finishEdge handle result middle).checked.native.machine.heap ∧
      (finishEdge handle result middle).edgeResults.cells handle = some ⟨original, .returned result⟩ ∧
      original.key = request.key := by
  obtain ⟨next, receipt, finalProbes⟩ := SourceCurrentAllocatedPartialEdgeActual.edge_call
    F S inventory (.evaluate (started := started) reads) ready admitted sound inherited resident
      correct stored covered ranges valid probes
  obtain ⟨_, cell, _, key⟩ := SourceCurrentAllocatedPartialMemoSound.beginEdge_evaluate_sound
    F S request before sound inherited resident handle original running started
  have same : middle.edgeResults = running.edgeResults := by cases body <;> rfl
  have current : middle.edgeResults.cells handle = some ⟨original, .evaluating⟩ := by
    rw [same]
    exact cell
  exact ⟨next, receipt, finalProbes,
    finishEdge_returned handle original result middle current, key⟩

/-- Raw contradiction makes the new body range condition vacuous. -/
theorem rejected_ranges (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (rejected : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = true) :
    SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before := by
  intro live
  rw [rejected] at live
  contradiction

/-- Every raw edge body retains the complete edge-result table before its own finish. -/
theorem body_table {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (body : EdgeBody budget request before result after) : after.edgeResults = before.edgeResults := by
  cases body
  rfl

#print axioms same_owner
#check @same_owner
#print axioms rejected_ranges
#check @rejected_ranges
#print axioms body_table
#check @body_table
end MicroCFTA.PartialEdgeActualIndependent
