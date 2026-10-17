import MicroCFTA.SourceMergedComparisonReplayStages
import MicroCFTA.SourceMergedComparisonStability
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace MicroCFTA.ComparisonStageIntegration
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open MergedSourceComparison (children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonReplayStages
private def expression : Syntax Nat Bool := .node [.mk 9 true [
  .node [.mk 7 true [.node [.mk 0 true []]], .mk 7 true [.node [.mk 1 true []]], .mk 8 true [.node [.mk 1 true []]]],
  .node [.mk 7 true [.node [.mk 1 true []]], .mk 8 true [.node [.mk 1 true []]]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def source := built.state
private def wide := (InternedProbeProvenance.children root).getD 0 .empty
private def narrow := (InternedProbeProvenance.children root).getD 1 .empty
private def wides := InternedEdgeResidency.nodeEdges wide
private def narrows := InternedEdgeResidency.nodeEdges narrow
private def defaultEdge : EdgeValue Nat Bool := (run (makeEdge 99 true []) empty).1
private def row := narrows.getD 0 defaultEdge
private def candidate := wides.getD 0 defaultEdge
private def limit := maximumDepth (InternedRecordCoherence.nodeInventory source) + 1
private def first : Value Nat Bool → Value Nat Bool → State Nat Bool → MergedSourceComparison.Result Nat Bool Bool := check (fun guard : Bool => guard) 2 []
private def second : Value Nat Bool → Value Nat Bool → State Nat Bool → MergedSourceComparison.Result Nat Bool Bool := check (fun guard : Bool => guard) 4 []
private theorem constructed : built = .done root source := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady source :=
  SourceEqualityRequiredSemanticCache.constructed expression root source constructed
private theorem bounded : InternedMuDepthInventory.Bounded source limit :=
  InternedMuDepthInventory.initial_bounded source semantic.ready.semantic.1.normal.facts
private theorem availableRoot : Available source root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root source constructed
private theorem wideAvailable : Available source wide :=
  availableRoot.children wide (by cbv; exact List.mem_cons_self)
private theorem narrowAvailable : Available source narrow :=
  availableRoot.children narrow (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem wideEdges : InternedNestedProvenance.Edges source wides :=
  InternedEdgeResidency.resident_edges source semantic.ready.semantic.1.normal.facts.linked wide wideAvailable.resident
private theorem narrowEdges : InternedNestedProvenance.Edges source narrows :=
  InternedEdgeResidency.resident_edges source semantic.ready.semantic.1.normal.facts.linked narrow narrowAvailable.resident
private theorem rowAvailable : InternedNestedProvenance.Values source row.children :=
  semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row (narrowEdges row (by cbv; exact List.mem_cons_self))
private theorem oldRecorded : SourceMergedComparisonHistory.Callback limit first :=
  SourceMergedComparisonHistory.check_recorded limit (fun guard : Bool => guard) 2 []
private theorem replay : CallbackReplay limit source first second := by
  intro left right before _semantic _bounded _leftAvailable _rightAvailable _leftClosed _rightClosed _reached answer after done
  exact SourceMergedComparisonStability.check_refines (fun guard : Bool => guard) 2 2 [] left right before answer after done
private theorem failedCandidate : MergedSourceComparison.children first candidate.children row.children source = .done false source := by cbv
private theorem oldCover : anyCover (fun guard : Bool => guard) first row wides source = .done true source := by cbv
private theorem oldRows : allRows 1 (fun guard : Bool => guard) first wide narrows source = .done true source := by cbv

/-- A real failed child cover precedes a successful later candidate under exact replay. -/
theorem failed_then_success :
    built = .done root source ∧
    MergedSourceComparison.children first candidate.children row.children source = .done false source ∧
    anyCover (fun guard : Bool => guard) first row wides source = .done true source ∧
    anyCover (fun guard : Bool => guard) second row wides source = .done true source := by
  have replayed := anyCover_replay limit source (fun guard : Bool => guard) first second oldRecorded replay row wides source
    semantic bounded rowAvailable wideEdges (by cbv; simp_all) (by cbv; simp_all) (.refl source) true source oldCover
  exact ⟨constructed, failedCandidate, oldCover, replayed⟩

/-- Two original narrow rows replay through repeated wide reads and their ordered covers. -/
theorem two_rows_replay :
    built = .done root source ∧ narrows.length = 2 ∧ wides.length = 3 ∧
    allRows 1 (fun guard : Bool => guard) first wide narrows source = .done true source ∧
    allRows 3 (fun guard : Bool => guard) second wide narrows source = .done true source := by
  have replayed := allRows_replay limit source 1 3 (fun guard : Bool => guard) first second oldRecorded replay
    (by
      intro value before _semantic _bounded _available _closed _reached rows after done
      exact SourceMergedComparisonStability.read_refines 1 2 value before rows after done)
    wide narrows source semantic bounded wideAvailable narrowEdges (by cbv) (by cbv; simp_all) (.refl source) true source oldRows
  exact ⟨constructed, by cbv, by cbv, oldRows, replayed⟩
end MicroCFTA.ComparisonStageIntegration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.ComparisonStageIntegration.failed_then_success
#check @MicroCFTA.ComparisonStageIntegration.failed_then_success
#print axioms MicroCFTA.ComparisonStageIntegration.two_rows_replay
#check @MicroCFTA.ComparisonStageIntegration.two_rows_replay
