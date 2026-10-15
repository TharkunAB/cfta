import MicroCFTA.SourceEqualityOnePassAPI
import MicroCFTA.SourceEqualitySelectedFoldSource

/-!
# Finite complete guarded native passes from closed source construction

Actual source prechecks choose every branch. The live branch derives
selection and required-path progress and retains both source memo receipts.
Native initialization and local reached word checks derive the remaining
finite pass. No completed whole-pass execution or global leaf law is supplied.
-/
namespace MicroCFTA.SourceEqualityOnePassSource
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityClassFoldGraph SourceEqualityNativeInitial SourceEqualityOnePassGraph
open SourceEqualityOnePassWorkerProofs
open SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}

/-- Actual live stage receipts retain both source memo call graphs and their returned cache validity. -/
def StageMemos {records values before queries middle required heap results after}
    (stages : SourceEqualitySelectedClassFold.Execution source emptyGuard conjoin clear top records values
      (before : NativeState width Symbol Guard) queries middle required heap results after) : Prop :=
  ∃ unfolding predicate,
    SourceMemoClassSelection.Reads values stages.stages.selection InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty unfolding predicate ∧
    SourcePredicateGateTrace.Keeps before.machine.heap middle unfolding predicate

/-- Source memo certificates retain exactly the queries executed by each graph branch. -/
inductive MemoReads {checked : Except String SourceEqualityPrecheck.Branch} {values : List (Value Symbol Guard)}
    {before : NativeState width Symbol Guard} :
    {answer : Except String (List (Value Symbol Guard))} → {after : NativeState width Symbol Guard} →
      Graph source emptyGuard conjoin clear top checked values before answer after → Prop where
  | error (actual : checked = .error message) : MemoReads (.error actual)
  | unchanged (actual : checked = .ok .unchanged) : MemoReads (.unchanged actual)
  | emptyChildren (actual : checked = .ok .emptyChildren) : MemoReads (.emptyChildren actual)
  | live (actual : checked = .ok (.classes records))
      (stages : SourceEqualitySelectedClassFold.Execution source emptyGuard conjoin clear top records values before queries middle required heap results after)
      (reads : StageMemos stages) : MemoReads (.live actual stages)

/-- Source gate and required-path progress derive complete stable native execution for every source precheck branch. -/
theorem complete (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (node : InternedFreshOrdinaryGateRank.Node Symbol Guard) (values : List (Value Symbol Guard))
    (own inherited : SourceEqualityPrecheck.Constraint) (semantic : SemanticReady node.state)
    (available : Values node.state values) (closed : ClosedValues values)
    (ranges : Ranges source emptyGuard conjoin clear top (SourceEqualityPrecheck.precheck own inherited) values (cold width node.state)) :
    ∃ results after, ∃ trace : Execution source emptyGuard conjoin clear top own inherited values (cold width node.state) (.ok results) after,
      MemoReads trace ∧ IdleReady emptyGuard conjoin after ∧ Keeps node.state after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      StableRun (fun g e p h c n => SourceEqualityOnePassWorker.run source emptyGuard conjoin clear top g e p h c n own inherited values (cold width node.state)) (.ok results) after ∧
      ∃ arrayBound, ∀ work, arrayBound ≤ work →
        StableRun (fun g e p h c n => SourceEqualityOnePassWorker.runArray source emptyGuard conjoin clear top work g e p h c n own inherited values (cold width node.state)) (.ok results) after := by
  have nativeReady := SourceEqualityNativeInitial.ready width emptyGuard conjoin node.state semantic
  obtain ⟨branch, checked⟩ := SourceEqualityPrecheck.precheck_safe own inherited
  cases branch with
  | unchanged =>
      let trace : Execution source emptyGuard conjoin clear top own inherited values (cold width node.state) (.ok values) (cold width node.state) := .unchanged checked
      exact ⟨values, _, trace, .unchanged checked, nativeReady, pure_keeps _ semantic.ready, available, closed,
        SourceEqualityOnePassAPI.stable source emptyGuard conjoin clear top trace, SourceEqualityOnePassAPI.array_stable source emptyGuard conjoin clear top trace⟩
  | emptyChildren =>
      let results := EqualityLeafProjectionRuntimeEmpty.erase values
      let trace : Execution source emptyGuard conjoin clear top own inherited values (cold width node.state) (.ok results) (cold width node.state) := .emptyChildren checked
      have scope := SourceEqualityEmptyPropagation.erased_scope node.state values
      exact ⟨results, _, trace, .emptyChildren checked, nativeReady, pure_keeps _ semantic.ready, scope.1, scope.2,
        SourceEqualityOnePassAPI.stable source emptyGuard conjoin clear top trace, SourceEqualityOnePassAPI.array_stable source emptyGuard conjoin clear top trace⟩
  | classes records =>
      have plans : ∀ queries middle required heap, SourceEqualitySelectedRequired.Execution source values (records.map SourceEqualityClassOrder.Record.paths)
          node.state queries middle required heap → SourceEqualityClassFoldGraph.Ranges emptyGuard conjoin clear top
            (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap (cold width node.state) heap) := by
        simpa only [SourceEqualityOnePassGraph.Ranges, checked, cold, SourceRecursiveIntersectionThunks.initial] using ranges
      obtain ⟨bound, queries, middle, required, heap, results, after, unfolding, predicate, stages, reads, kept, finalReady, keeps, resident, resultClosed, _, _, _⟩ :=
        SourceEqualitySelectedFoldSource.complete width emptyGuard conjoin clear top node values records semantic available closed plans
      let trace : Execution source emptyGuard conjoin clear top own inherited values (cold width node.state) (.ok results) after := .live checked stages
      exact ⟨results, after, trace, .live checked stages ⟨unfolding, predicate, reads, kept⟩, finalReady, keeps, resident, resultClosed,
        SourceEqualityOnePassAPI.stable source emptyGuard conjoin clear top trace, SourceEqualityOnePassAPI.array_stable source emptyGuard conjoin clear top trace⟩

/-- Original closed source construction derives complete guarded equality passes for every original outgoing child forest. -/
theorem source_edges (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (expression : InternedNestedConstruction.Syntax Symbol Guard) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ own inherited,
        Ranges source emptyGuard conjoin clear top (SourceEqualityPrecheck.precheck own inherited) edge.children (cold width heap) →
          ∃ results after, ∃ trace : Execution source emptyGuard conjoin clear top own inherited edge.children (cold width heap) (.ok results) after,
            MemoReads trace ∧ IdleReady emptyGuard conjoin after ∧ Keeps heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
            StableRun (fun g e p h c n => SourceEqualityOnePassWorker.run source emptyGuard conjoin clear top g e p h c n own inherited edge.children (cold width heap)) (.ok results) after := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built
  let node := InternedFreshOrdinaryGateRank.fromCompleted expression value heap built
  refine ⟨value, heap, built, ?_⟩
  intro entry edges depth free original edge member own inherited ranges
  have facts := semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges heap facts.linked value available.resident
  rw [original] at resident
  have childAvailable := facts.cached.edges edge.entry.key edge (resident edge member)
  have childClosed : ClosedValues edge.children := by
    rw [original] at available closed
    exact MergedColdReaderClosed.node_children_closed heap facts entry edges depth free available closed edge member
  obtain ⟨results, after, trace, reads, finalReady, keeps, resultAvailable, resultClosed, stable, _⟩ :=
    complete width emptyGuard conjoin clear top node edge.children own inherited semantic childAvailable childClosed ranges
  exact ⟨results, after, trace, reads, finalReady, keeps, resultAvailable, resultClosed, stable⟩

end MicroCFTA.SourceEqualityOnePassSource
