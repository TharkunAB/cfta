import MicroCFTA.SourceCurrentAllocatedPartialMemoSound

namespace MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialMemoSound
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "MergeMemo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
variable {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

-- A cold edge start derives the actual evaluating owner without any result law.
theorem cold_edge_start (checked : Checked width) (merge : MergeMemo) (fourth : Fourth) (request : EdgeRequest)
    (inherited : EqReady checked.operations.constraints request.inherited)
    (resident : Resident checked.native.machine.heap request.value) :
    let before := initial checked merge fourth
    let running := (beginEdge request before).2.2
    (beginEdge request before).1 = 0 ∧ (beginEdge request before).2.1 = .evaluate request ∧
      Sound formulas solver running ∧ running.edgeResults.cells 0 = some ⟨request, .evaluating⟩ ∧
      EdgeGood formulas solver running.checked ⟨request, .evaluating⟩ := by
  let before := initial checked merge fourth
  let running := (beginEdge request before).2.2
  have first := beginEdge_fresh request before rfl
  have handles : (beginEdge request before).1 = 0 := congrArg Prod.fst first.1
  have observed : (beginEdge request before).2.1 = .evaluate request := congrArg (fun value => value.2.1) first.1
  have actual : beginEdge request before = (0, .evaluate request, running) :=
    Prod.ext handles (Prod.ext observed rfl)
  have started := beginEdge_evaluate_sound formulas solver request before
    (initial_sound formulas solver checked merge fourth) inherited resident 0 request running actual
  exact ⟨handles, observed, started.1, started.2.1, started.2.2.1⟩

-- Finishing a proved body makes a later equal-key candidate a literal unchanged-state hit.
theorem edge_finish_then_alias_hit (before : Caller width) (sound : Sound formulas solver before)
    (original candidate : EdgeRequest) (handle : Nat) (result : Edge)
    (published : before.edgeResults.table candidate.key = some handle)
    (running : before.edgeResults.cells handle = some ⟨original, .evaluating⟩)
    (candidateReady : EqReady before.checked.operations.constraints candidate.inherited)
    (candidateResident : Resident before.checked.native.machine.heap candidate.value)
    (resident : Resident before.checked.native.machine.heap result)
    (bodyLaw : EdgeLaw formulas solver original result)
    (valid : Cache.Valid before.checked.operations.constraints)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap) :
    let after := finishEdge handle result before
    Sound formulas solver after ∧ beginEdge candidate after = (handle, .ready result, after) ∧
      Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver candidate result := by
  let after := finishEdge handle result before
  have completed := finishEdge_sound formulas solver handle original result before sound running resident bodyLaw
  have returned := finishEdge_returned handle original result before running
  have table : after.edgeResults.table candidate.key = some handle := by
    simpa only [after, finishEdge, FlatMemoThunk.finish, running, FlatMemoThunk.setStatus] using published
  have hit := beginEdge_ready candidate original after handle result table returned
  have checked := beginEdge_ready_sound formulas solver candidate after completed valid coherent candidateReady
    candidateResident handle result after hit
  exact ⟨completed, hit, checked.2.1, checked.2.2⟩

-- The node family has its own completed law and does not require the edge table to be cold.
theorem node_finish_then_alias_hit (before : Caller width) (sound : Sound formulas solver before)
    (original candidate : NodeRequest) (handle : Nat) (result : Node)
    (published : before.nodeResults.table candidate.key = some handle)
    (running : before.nodeResults.cells handle = some ⟨original, .evaluating⟩)
    (candidateReady : EqReady before.checked.operations.constraints candidate.inherited)
    (candidateAvailable : Available before.checked.native.machine.heap candidate.value)
    (available : Available before.checked.native.machine.heap result)
    (bodyLaw : NodeLaw formulas solver original result)
    (valid : Cache.Valid before.checked.operations.constraints)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap) :
    let after := finishNode handle result before
    Sound formulas solver after ∧ beginNode candidate after = (handle, .ready result, after) ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver candidate result := by
  let after := finishNode handle result before
  have completed := finishNode_sound formulas solver handle original result before sound running available bodyLaw
  have returned := finishNode_returned handle original result before running
  have table : after.nodeResults.table candidate.key = some handle := by
    simpa only [after, finishNode, FlatMemoThunk.finish, running, FlatMemoThunk.setStatus] using published
  have hit := beginNode_ready candidate original after handle result table returned
  have checked := beginNode_ready_sound formulas solver candidate after completed valid coherent candidateReady
    candidateAvailable handle result after hit
  exact ⟨completed, hit, checked.2.1, checked.2.2⟩

-- Physical equality allocation and heap growth retain the warm edge law and complete state hit.
theorem physical_growth_retains_edge_hit (before : Caller width) (checked : Checked width)
    (fourth : Fourth) (merge : MergeMemo) (sound : Sound formulas solver before)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical checked))
    (candidate original : EdgeRequest) (handle : Nat) (result : Edge)
    (published : before.edgeResults.table candidate.key = some handle)
    (returned : before.edgeResults.cells handle = some ⟨original, .returned result⟩)
    (candidateReady : EqReady before.checked.operations.constraints candidate.inherited)
    (candidateResident : Resident before.checked.native.machine.heap candidate.value)
    (valid : Cache.Valid checked.operations.constraints)
    (coherent : InternedRecordCoherence.Coherent checked.native.machine.heap) :
    let after := advance before checked fourth merge
    Sound formulas solver after ∧ beginEdge candidate after = (handle, .ready result, after) ∧
      Resident checked.native.machine.heap result ∧ EdgeLaw formulas solver candidate result := by
  let after := advance before checked fourth merge
  have moved := sound.advance formulas solver checked fourth merge effects
  have hit := beginEdge_ready candidate original after handle result published returned
  have ready := candidateReady.grows effects.grows.constraint_growth
  have resident := InternedEdgeResidency.edge_grows _ _ effects.keeps.growth _ candidateResident
  have reuse := beginEdge_ready_sound formulas solver candidate after moved valid coherent ready resident handle result after hit
  exact ⟨moved, hit, reuse.2.1, reuse.2.2⟩

end MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes

#print axioms MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.cold_edge_start
#print axioms MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.edge_finish_then_alias_hit
#print axioms MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.node_finish_then_alias_hit
#print axioms MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.physical_growth_retains_edge_hit
#check @MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.cold_edge_start
#check @MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.edge_finish_then_alias_hit
#check @MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.node_finish_then_alias_hit
#check @MicroCFTA.SourceCurrentAllocatedPartialMemoSoundProbes.physical_growth_retains_edge_hit
