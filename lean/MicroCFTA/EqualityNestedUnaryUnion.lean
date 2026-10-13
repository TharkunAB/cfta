import MicroCFTA.EqualityNestedUnaryBound

/-!
# Exact projected unions of generated nested endpoints

The actual union constructor retains exactly the represented nested rows
from all original occurrences. Empty operands and repeated physical nodes
use the source constructor branches. No global cache preparation is needed.
-/
namespace MicroCFTA.EqualityNestedUnaryUnion
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct EqualityMergedTargetReadback

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Exact constructor readback excludes reference, recursive, and union roots. -/
theorem normal_ordinary (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (available : Available state value) (normal : Replayable value) :
    EqualityLeafProjectionUnion.OrdinaryRoot value := by
  have readback := replayable_normal value normal state facts available
  have ordinary := EqualityLeafProjectionUnion.makeNode_ordinary (nodeEdges value) state facts.coherent facts.linked
    (resident_edges state facts.linked value available.resident)
  rw [readback] at ordinary
  exact ordinary

/-- The exact union row predicate retains all original occurrence inputs. -/
def Project (inputs : List (Node initial × Value (Fin symbols) ConstraintKey)) : Node initial :=
  fun row => ∃ input ∈ inputs, input.1 row

/-- Actual source union returns exactly the projected generated row set and canonical readback. -/
theorem union_complete (parent leaf : Fin symbols) (inputs : List (Node initial × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (valid : ∀ input ∈ inputs, Available state input.2 ∧ Replayable input.2 ∧ NodeShape parent leaf input.1 input.2) :
    Complete (fun _ => MergedColdMerge.work (makeUnion (inputs.map Prod.snd))) state
      (fun after result => Available after result ∧ Replayable result ∧ NodeShape parent leaf (Project inputs) result) := by
  let values := inputs.map Prod.snd
  have available : Values state values := by
    intro value member
    obtain ⟨input, included, rfl⟩ := List.mem_map.mp member
    exact (valid input included).1
  have normal : ∀ value ∈ values, EqualityOrdinaryReadback.Normal state value := by
    intro value member
    obtain ⟨input, included, rfl⟩ := List.mem_map.mp member
    exact replayable_normal input.2 (valid input included).2.1 state facts (valid input included).1
  have ordinary : ∀ value ∈ values, EqualityLeafProjectionUnion.OrdinaryRoot value := by
    intro value member
    obtain ⟨input, included, rfl⟩ := List.mem_map.mp member
    exact normal_ordinary input.2 state facts (valid input included).1 (valid input included).2.1
  have live : ∀ value ∈ values, ∀ edge ∈ nodeEdges value, EqualityLeafProjectionPhysical.dead edge = false := by
    intro value member edge present
    obtain ⟨input, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨row, _, shape⟩ := (valid input included).2.2.sound edge present
    exact row_live parent leaf row edge shape
  have verified := union_verified values state facts available
  let result := run (makeUnion values) state
  have resultAvailable : Available result.2 result.1 := verified.result _ _ rfl
  have readback := EqualityOrdinaryReadback.makeUnion_normal values state facts.coherent facts.linked
    (fun value member => (available value member).resident) ordinary normal
  have membership := EqualityLeafProjectionUnion.union_edges values state facts.coherent facts.linked
    (fun value member => (available value member).resident) ordinary live
  apply MergedColdMergeSoundness.work_post _ state prepared Available _ verified (makeUnion_noNewMu values state)
  refine ⟨resultAvailable, ⟨result.2, verified.facts, resultAvailable, readback⟩, ?_⟩
  constructor
  · intro edge member
    obtain ⟨value, valueMember, present⟩ := (membership edge).mp member
    obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp valueMember
    obtain ⟨row, selected, shape⟩ := (valid input inputMember).2.2.sound edge present
    exact ⟨row, ⟨input, inputMember, selected⟩, shape⟩
  · rintro row ⟨input, included, selected⟩
    obtain ⟨edge, member, shape⟩ := (valid input included).2.2.complete row selected
    exact ⟨edge, (membership edge).mpr ⟨input.2, List.mem_map.mpr ⟨input, included, rfl⟩, member⟩, shape⟩

/-- Projection followed by the current target merge keeps the exact generated row set. -/
theorem target_complete (parent leaf : Fin symbols) (inputs : List (Node initial × Value (Fin symbols) ConstraintKey))
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (valid : ∀ input ∈ inputs, Available state input.2 ∧ Replayable input.2 ∧ NodeShape parent leaf input.1 input.2)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    Complete (fun _ => MergedColdMerge.bind (MergedColdMerge.work (makeUnion (inputs.map Prod.snd)))
      (execute MergedSourceGrouping.groups clear top comparison)) state
      (fun after result => Available after result ∧ Replayable result ∧ NodeShape parent leaf (Project inputs) result) := by
  apply bind_complete _ _ state _ _ (union_complete parent leaf inputs state facts prepared valid)
  intro value after extension property
  have fixed := EqualityNestedUnaryBound.merge_fixed parent leaf (Project inputs) value small property.2.2 property.2.1
    after extension.facts extension.prepared property.1 clear top comparison
  exact ⟨0, value, after, fun _ _ => fixed, .refl after extension.facts extension.prepared, property⟩

end MicroCFTA.EqualityNestedUnaryUnion
