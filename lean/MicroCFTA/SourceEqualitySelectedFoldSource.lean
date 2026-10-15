import MicroCFTA.SourceEqualitySelectedClassFold
import MicroCFTA.SourceEqualityNativeInitial

/-!
# Finite selected class processing from closed source construction

Actual source gate selection and required paths derive their complete
stages. Local reached word checks derive the remaining native fold. Cold
native validity follows from the actual constructor heap. Source gate memo
receipts and independent finite bounds remain explicit in the result.
-/
namespace MicroCFTA.SourceEqualitySelectedFoldSource
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityClassFoldGraph SourceEqualitySelectedClassFold SourceEqualityNativeInitial
open InternedSourceClassSelection (Query selected select)
open SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat)
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Original source gate and required-path progress plus actual native word checks derive complete selected processing. -/
theorem complete (node : InternedFreshOrdinaryGateRank.Node Symbol Guard) (values : List (Value Symbol Guard))
    (records : List SourceEqualityClassOrder.Record) (semantic : SemanticReady node.state) (available : Values node.state values) (closed : ClosedValues values)
    (ranges : ∀ queries middle required heap, SourceEqualitySelectedRequired.Execution source values (records.map SourceEqualityClassOrder.Record.paths)
      node.state queries middle required heap → Ranges emptyGuard conjoin clear top (SourceEqualitySelectedRecords.keep records queries) required
        (advanceHeap (cold width node.state) heap)) :
    ∃ gateBound queries, ∃ middle : InternedFreshOrdinaryGateRank.Node Symbol Guard, ∃ required heap results after unfolding predicate,
      ∃ trace : Execution source emptyGuard conjoin clear top records values (cold width node.state) queries middle.state required heap results after,
        SourceMemoClassSelection.Reads values trace.stages.selection InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty unfolding predicate ∧
        SourcePredicateGateTrace.Keeps node.state middle.state unfolding predicate ∧
        IdleReady emptyGuard conjoin after ∧ Keeps node.state after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
        (∀ extra, select source (gateBound + extra) values (records.map SourceEqualityClassOrder.Record.paths) node.state = .done (some (selected queries)) middle.state) ∧
        SourceEqualityRequiredWorkerComplete.StableRun
          (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths (selected queries)) values middle.state) required heap ∧
        SourceEqualityClassFoldWorkerProofs.StableRun
          (fun e p h c n => SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n
            (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap (cold width node.state) heap)) results after := by
  obtain ⟨bound, queries, middle, required, heap, unfolding, predicate, stages, reads, kept, _, gateStable, requiredStable⟩ :=
    SourceEqualitySelectedRequired.complete node values (records.map SourceEqualityClassOrder.Record.paths) semantic available closed
  have nativeReady := SourceEqualityNativeInitial.ready width emptyGuard conjoin node.state semantic
  obtain ⟨results, after, trace, finalReady, keeps, resident, resultClosed, stable⟩ :=
    after_prefix (width := width) (emptyGuard := emptyGuard) (conjoin := conjoin) (clear := clear) (top := top)
      stages nativeReady available closed (ranges queries middle.state required heap stages)
  exact ⟨bound, queries, middle, required, heap, results, after, unfolding, predicate, trace, reads, kept,
    finalReady, keeps, resident, resultClosed, gateStable, requiredStable, stable⟩

/-- Closed original construction supplies all initial constructor, child, and cold native invariants for the selected live branch. -/
theorem source_edges (expression : InternedNestedConstruction.Syntax Symbol Guard) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges,
        ∀ own inherited records, SourceEqualityPrecheck.precheck own inherited = .ok (.classes records) →
          (∀ queries middle required final, SourceEqualitySelectedRequired.Execution source edge.children (records.map SourceEqualityClassOrder.Record.paths)
            heap queries middle required final → Ranges emptyGuard conjoin clear top (SourceEqualitySelectedRecords.keep records queries) required
              (advanceHeap (cold width heap) final)) →
          ∃ queries middle required final results after unfolding predicate,
            SourceEqualitySelectionEntry.Execution edge.children own inherited heap InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty
              (.selected (selected queries)) middle unfolding predicate ∧
            Execution source emptyGuard conjoin clear top records edge.children (cold width heap) queries middle required final results after ∧
            IdleReady emptyGuard conjoin after ∧ Keeps heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
            SourceEqualityClassFoldWorkerProofs.StableRun
              (fun e p h c n => SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n
                (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap (cold width heap) final)) results after := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built
  let node := InternedFreshOrdinaryGateRank.fromCompleted expression value heap built
  refine ⟨value, heap, built, ?_⟩
  intro entry edges depth free original edge member own inherited records checked ranges
  have facts := semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges heap facts.linked value available.resident
  rw [original] at resident
  have childAvailable := facts.cached.edges edge.entry.key edge (resident edge member)
  have childClosed : ClosedValues edge.children := by
    rw [original] at available closed
    exact MergedColdReaderClosed.node_children_closed heap facts entry edges depth free available closed edge member
  obtain ⟨bound, queries, middle, required, final, results, after, unfolding, predicate, trace, reads, _, finalReady, keeps, resultAvailable, resultClosed, _, _, stable⟩ :=
    complete width emptyGuard conjoin clear top node edge.children records semantic childAvailable childClosed ranges
  exact ⟨queries, middle.state, required, final, results, after, unfolding, predicate, .select checked trace.stages.selection reads,
    trace, finalReady, keeps, resultAvailable, resultClosed, stable⟩

end MicroCFTA.SourceEqualitySelectedFoldSource
