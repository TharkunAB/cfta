import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardFinite

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option format.width 200

namespace MicroCFTA.MergeGuardIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Top" => SourceEqualityConstraintConstructors.top
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Certificate" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Certificate
local notation "Guards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "Physical" => SourceCurrentMemoMergeEffects.Stored
local notation "GNode" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
variable [DecidableEq Symbol] [edgeEq : DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- An actual miss derives its own candidate law before a second same-state warm call. -/
theorem actual_miss_then_warm {clear : Guard → Bool} {input candidate : Value Symbol Guard}
    {before after : State Symbol Guard} {current : Memo Symbol Guard}
    (body : Run clear Top (SourceCurrentMemoMergeGraph.body Top input) before empty candidate after current)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (limits : Limits) (profile : GNode limits input) :
    let saved := remember current input candidate
    let output := (winner current input candidate).result
    Call clear Top input before empty output after saved ∧
      Call clear Top input after saved output after saved ∧
      Physical after saved ∧ Guards saved ∧ Certificate input output ∧ GNode limits output := by
  dsimp only
  have first : Call clear Top input before empty (winner current input candidate).result after (remember current input candidate) :=
    .miss rfl body
  have result := SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer.cold first semantic costs available
  have warm : Call clear Top input after (remember current input candidate)
      (winner current input candidate).result after (remember current input candidate) := .hit (winner_found current input candidate)
  have repeated := SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer.call_guard warm result.1.semantic result.1.costs
    result.2.1 result.2.2.1 (result.1.keeps.available input available)
  exact ⟨first, warm, repeated.2.1, repeated.2.2.1, repeated.2.2.2.2, repeated.2.2.2.2 limits profile⟩

/-- An earlier reentrant winner uses its actual derived law, without a candidate-law input. -/
theorem actual_reentrant_winner {clear : Guard → Bool} {input candidate : Value Symbol Guard}
    {before after : State Symbol Guard} {current : Memo Symbol Guard} {entry : Entry Symbol Guard}
    (body : Run clear Top (SourceCurrentMemoMergeGraph.body Top input) before empty candidate after current)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (found : current input.referenceOf = some entry) :
    remember current input candidate = current ∧ winner current input candidate = entry ∧
      Physical after current ∧ Guards current ∧ Certificate input entry.result := by
  have actual : Call clear Top input before empty (winner current input candidate).result after (remember current input candidate) :=
    .miss rfl body
  have result := SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer.cold actual semantic costs available
  have retained := winner_existing current input candidate entry found
  exact ⟨retained.1, retained.2, by simpa only [retained.1] using result.2.1,
    by simpa only [retained.1] using result.2.2.1, by simpa only [retained.2] using result.2.2.2.2⟩

/-- Five literal rows select the Top branch while retaining every nested child bound. -/
theorem five_row_actual (clear : Guard → Bool)
    (first second third fourth fifth : EdgeValue Symbol Guard) (before after : State Symbol Guard)
    (memo saved : Memo Symbol Guard) (outputs : List (EdgeValue Symbol Guard))
    (actual : Run clear Top (group Top [first, second, third, fourth, fifth]) before memo outputs after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (physical : Physical before memo) (guards : Guards memo)
    (resident : Edges before [first, second, third, fourth, fifth]) (limits : Limits)
    (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows limits [first, second, third, fourth, fifth]) :
    group Top [first, second, third, fourth, fifth] = .bind (large Top first [second, third, fourth, fifth]) (fun edge => .pure [edge]) ∧
      Physical after saved ∧ Guards saved ∧ ∀ edge ∈ outputs,
        EdgeResident after edge ∧ SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits edge := by
  have certified := SourceCurrentAllocatedFiniteOrdinaryMergeGuardBody.group_certified clear
    [first, second, third, fourth, fifth] before semantic costs resident limits profile
  have produced := SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer.run_guard actual _ semantic costs physical guards certified
  exact ⟨by simp [group], produced.2⟩

/-- An ordered actual request map retains a separate universal law at every original position. -/
theorem ordered_actual_requests (clear : Guard → Bool) (inputs outputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (memo saved : Memo Symbol Guard)
    (actual : Run clear Top (map Code.request inputs) before memo outputs after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (physical : Physical before memo) (guards : Guards memo)
    (available : Values before inputs) :
    Physical after saved ∧ Guards saved ∧
      Language.All₂ (fun original output => Available after output ∧ Certificate original output) inputs outputs ∧
      outputs.length = inputs.length := by
  have checked := SourceCurrentAllocatedFiniteOrdinaryMergeGuardCode.map_certified clear Code.request
    (fun heap value => Available heap value) (fun heap original output => Available heap output ∧ Certificate original output)
    (fun _ _ effect value ready => effect.keeps.available value ready)
    (fun _ _ effect _ value ready => ⟨effect.keeps.available value ready.1, ready.2⟩) inputs
    (fun value _ heap _ _ ready => (SourceCurrentAllocatedFiniteOrdinaryMergeGuardCode.request_certified clear value heap ready).mono
      (fun _ _ returned => ⟨returned.1.1, returned.2⟩)) before semantic costs available
  have result := SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer.run_guard actual _ semantic costs physical guards checked
  exact ⟨result.2.1, result.2.2.1, result.2.2.2, result.2.2.2.length_eq.symm⟩

end MicroCFTA.MergeGuardIndependent

namespace MicroCFTA.MergeGuardAllocatedIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "State" => SourceCurrentAllocatedMergeGraph.State
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "Node" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial bounds construct a whole allocated call and an exact one-work-bound warm reuse. -/
theorem constructed_then_literal_hit (clear : Guard → Bool) (input : Value Symbol Guard) (before : State)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Available before.heap input)
    (limits : Limits) (profile : Node limits input) :
    ∃ output after saved,
      SourceCurrentAllocatedMergeGraph.Call clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentAllocatedMergeWorkerCompletion.StableCall clear input before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧
      SourceCurrentMemoMergeEffects.Stored after.heap saved ∧ Profiles saved ∧ Node limits output ∧
      SourceCurrentAllocatedMergeWorker.call clear 1 0 input after saved = .done output after saved := by
  obtain ⟨output, after, saved, actual, stable, effects, physical, profiles, _available, _certificate, outputProfile⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeGuardFinite.cold clear input before ready available limits profile
  obtain ⟨entry, found, same⟩ := actual.graph.present
  have warm := SourceCurrentAllocatedMergeWorker.call_hit clear 0 0 input after saved entry found
  exact ⟨output, after, saved, actual, stable, effects, physical, profiles, outputProfile, by simpa only [same] using warm⟩

end MicroCFTA.MergeGuardAllocatedIndependent

#print axioms MicroCFTA.MergeGuardIndependent.actual_miss_then_warm
#check @MicroCFTA.MergeGuardIndependent.actual_miss_then_warm
#print axioms MicroCFTA.MergeGuardIndependent.actual_reentrant_winner
#check @MicroCFTA.MergeGuardIndependent.actual_reentrant_winner
#print axioms MicroCFTA.MergeGuardIndependent.five_row_actual
#check @MicroCFTA.MergeGuardIndependent.five_row_actual
#print axioms MicroCFTA.MergeGuardIndependent.ordered_actual_requests
#check @MicroCFTA.MergeGuardIndependent.ordered_actual_requests
#print axioms MicroCFTA.MergeGuardAllocatedIndependent.constructed_then_literal_hit
#check @MicroCFTA.MergeGuardAllocatedIndependent.constructed_then_literal_hit
