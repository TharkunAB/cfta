import MicroCFTA.SourceCurrentPositionalRowOrigins
import MicroCFTA.SourceEqualityRequiredWorkerSound
import MicroCFTA.SourceEqualityRequiredComplete
set_option linter.all true
set_option maxHeartbeats 3000000
set_option cbv.maxSteps 10000000
set_option maxRecDepth 10000

namespace MicroCFTA.PositionalRowKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredGraph

private def tau : Syntax Nat Nat := .binder false (.node [.mk 1 0 [.var 0, .var 0]])
private def expression : Syntax Nat Nat := .node [.mk 2 17 [tau, tau]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def source : Value Nat Nat := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def needed : SourceEqualityNeeded.Needed := .node [(0, .node [(0, .node [])])]
private def adjusted := SourceEqualityRequiredWorker.require 8 8 needed source heap
private def output : Value Nat Nat := match adjusted with | .done value _ => value | _ => .empty
private def after : State Nat Nat := match adjusted with
  | .done _ state | .pending _ state | .unresolved _ state | .exhausted _ state => state
private def fallback : EdgeValue Nat Nat := (run (makeEdge 0 0 []) empty).1
private def original : EdgeValue Nat Nat := ((nodeEdges source)[0]?).getD fallback
private def returned : EdgeValue Nat Nat := ((nodeEdges output)[0]?).getD fallback

private theorem constructed : built = .done source heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, source, heap, done, InternedNestedConstruction.Outcome.state]

private theorem completed : adjusted = .done output after := by
  have tag : (match adjusted with | .done .. => true | _ => false) = true := by cbv
  cases found : adjusted <;> simp_all only [output, after, Bool.false_eq_true]

private theorem source_node : ∃ entry edges depth free, source = .node entry edges depth free := by
  have tag : (match source with | .node .. => true | _ => false) = true := by cbv
  cases found : source with
  | node entry edges depth free => exact ⟨entry, edges, depth, free, rfl⟩
  | empty | reference | union | mu => simp_all

private theorem source_rows : nodeEdges source = [original] := by cbv
private theorem returned_rows : nodeEdges output = [returned] := by cbv

private theorem witness :
    built = .done source heap ∧
    SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
    InternedFreshOrdinaryCostHeap.Heap heap ∧ Available heap source ∧
    RequireNode needed source heap output after ∧
    nodeEdges output = [returned] ∧ returned.entry.key.constraint = 17 ∧
    returned.children[1]? = original.children[1]? ∧
    returned.children[0]? ≠ original.children[0]? ∧
    (match original.children[1]? with | some (.mu ..) => true | _ => false) = true := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression source heap constructed
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, heap] using InternedFreshOrdinaryCosts.closed_heap expression
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result source heap constructed
  have graph := SourceEqualityRequiredWorkerSound.require_graph 8 8 needed source heap output after completed
  obtain ⟨entry, rows, depth, free, sourceShape⟩ := source_node
  have residentSource : rows = [original] := by simpa only [sourceShape, nodeEdges] using source_rows
  have selected : returned ∈ nodeEdges output := by rw [returned_rows]; exact List.mem_cons_self
  obtain ⟨index, earlier, found, fields, unchanged⟩ :=
    SourceCurrentPositionalRowOrigins.required_node
      (by simpa only [needed, sourceShape] using graph)
      semantic costs (by simpa only [sourceShape] using available) 1 rfl returned selected
  have same : earlier = original := by
    have member := List.mem_of_getElem? found
    rw [residentSource] at member
    exact List.mem_singleton.mp member
  subst earlier
  have guard : original.entry.key.constraint = 17 := by cbv
  have changed : returned.children[0]? ≠ original.children[0]? := by
    intro same
    have references := congrArg (Option.map Value.referenceOf) same
    cbv at references
    cases references
  have recursive : (match original.children[1]? with | some (.mu ..) => true | _ => false) = true := by cbv
  exact ⟨constructed, semantic, costs, available, graph, returned_rows,
    fields.1.trans guard, unchanged, changed, recursive⟩

/-- An actual source-built Mu child changes at selected zero and stays exact at unselected one. -/
theorem selected_mu_untouched_one :
    built = .done source heap ∧
    SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
    InternedFreshOrdinaryCostHeap.Heap heap ∧ Available heap source ∧
    RequireNode needed source heap output after ∧
    nodeEdges output = [returned] ∧ returned.entry.key.constraint = 17 ∧
    returned.children[1]? = original.children[1]? ∧
    returned.children[0]? ≠ original.children[0]? ∧
    (match original.children[1]? with | some (.mu ..) => true | _ => false) = true := witness

end MicroCFTA.PositionalRowKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.PositionalRowKernels.selected_mu_untouched_one
#print MicroCFTA.PositionalRowKernels.selected_mu_untouched_one
#print axioms MicroCFTA.PositionalRowKernels.selected_mu_untouched_one
