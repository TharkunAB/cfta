import MicroCFTA.SourceEqualityRequiredHead
import MicroCFTA.SourceFreshOrdinaryColdGuardedExact
import MicroCFTA.InternedGuardedBudgetExecution

/-!
# Semantic probe heaps through actual required-path constructors

The finite worker readiness remains unchanged. Independent language proofs
also retain the ordinary and budget probe-language heaps. Original source
construction derives these fields. Actual ordinary requests add no Mu record.
-/
namespace MicroCFTA.SourceEqualityRequiredSemanticCache
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredHead

/-- A complete worker cache also retains both independent probe-language heaps. -/
structure SemanticReady (state : State Symbol Guard) : Prop where
  ready : Ready state
  guarded : InternedGuardedProbeHeap.Heap state
  budget : InternedGuardedBudgetProbeHeap.Heap state

/-- Original closed source construction derives every semantic cache premise. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) : SemanticReady state := by
  refine ⟨SourceEqualityRequiredCache.constructed expression value state built, ?_, ?_⟩
  · simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  · simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedBudgetExecution.closed_heap expression

/-- Actual edge reconstruction preserves both semantic probe heaps and readiness. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (semantic : SemanticReady state)
    (available : Values state values) : SemanticReady (run (makeEdge symbol guard values) state).2 :=
  ⟨(SourceEqualityRequiredCache.edge symbol guard values state semantic.ready available).1.ready,
    semantic.guarded, semantic.budget⟩

/-- Actual row-node reconstruction preserves both semantic heaps without a whole-constructor meaning law. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (semantic : SemanticReady state) (resident : Edges state edges)
    (closed : MergedColdReaderClosedInputs.ClosedEdges edges) : SemanticReady (run (makeNode edges) state).2 :=
  ⟨(SourceEqualityRequiredCache.node edges state semantic.ready resident closed).1.ready,
    InternedGuardedProbeHeap.preserve state _ semantic.guarded (InternedShallowHeap.makeNode_noNewMu edges state),
    InternedGuardedBudgetProbeHeap.preserve state _ semantic.budget (InternedShallowHeap.makeNode_noNewMu edges state)⟩

/-- Actual cold exposure and row-node construction preserve all semantic cache fields. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Head value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) : SemanticReady after := by
  have checked := trace.verified semantic.ready available closed
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      have guarded : InternedGuardedProbeHeap.Heap middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using
          MergedFreshOrdinaryGuardedEffects.nodeEdges_heap fuel value before semantic.ready.semantic semantic.ready.covered
            semantic.guarded available closed
      have budget : InternedGuardedBudgetProbeHeap.Heap middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using
          MergedFreshOrdinaryBudgetEffects.nodeEdges_heap fuel value before semantic.ready.semantic semantic.ready.covered
            semantic.budget available closed
      have laterGuarded := InternedGuardedProbeHeap.preserve middle _ guarded (InternedShallowHeap.makeNode_noNewMu edges middle)
      have laterBudget := InternedGuardedBudgetProbeHeap.preserve middle _ budget (InternedShallowHeap.makeNode_noNewMu edges middle)
      refine ⟨checked.1.ready, ?_, ?_⟩
      · simpa only [rebuilt] using laterGuarded
      · simpa only [rebuilt] using laterBudget

end MicroCFTA.SourceEqualityRequiredSemanticCache
