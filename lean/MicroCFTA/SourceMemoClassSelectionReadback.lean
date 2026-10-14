import MicroCFTA.SourceMemoClassSelection
import MicroCFTA.InternedSourceClassSelectionReadback

/-!
# Original source class selection and pure reduction readback

Original construction supplies complete ordered selection with both source
memo tables. Every per-occurrence Boolean replays in the final cache.
The resulting class list is exactly the pure reduction's selected list.
-/
namespace MicroCFTA.SourceMemoClassSelection
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryGateRank (Node fromCompleted)
open InternedFreshOrdinaryMemoGateTrace (node_ready)
open InternedSourceClassSelection (Query Trace selected select guarded)
open SourcePredicateGateTrace (Keeps)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

/-- Original outgoing edges derive finite complete memo selection and exact pure selected-class readback. -/
theorem source_selected [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (ops : EqualityReduction.Operations (Value Symbol Guard) TermSymbol) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ classes,
        ∃ bound queries, ∃ after : Node Symbol Guard, ∃ savedUnfold savedPredicate,
          ∃ trace : Trace source edge.children classes state queries after.state,
            Reads edge.children trace InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty savedUnfold savedPredicate ∧
              Keeps state after.state savedUnfold savedPredicate ∧
                selected queries = EqualityReduction.selectedClasses (guarded source after ops) classes edge.children ∧
                  ∀ extra, select source (bound + extra) edge.children classes state = .done (some (selected queries)) after.state := by
  obtain ⟨value, state, done, complete⟩ := source_edges expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member classes
  obtain ⟨bound, queries, after, savedUnfold, savedPredicate, trace, reads, kept, stable⟩ :=
    complete entry edges depth free original edge member classes
  let node := fromCompleted expression value state done
  have available : ∀ child ∈ edge.children, Available state child := by
    intro child selected
    apply node.available.children child
    change child ∈ InternedProbeProvenance.children value
    rw [original]
    exact List.mem_flatMap.mpr ⟨edge, member, selected⟩
  exact ⟨bound, queries, after, savedUnfold, savedPredicate, trace, reads, kept,
    trace.selected_eq_guarded after (node_ready node) available ops, stable⟩

end MicroCFTA.SourceMemoClassSelection
