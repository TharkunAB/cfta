import MicroCFTA.SourceEqualityAnnotationPass
import MicroCFTA.SourceEqualityNormalizedEntry

/-!
# Exact public language of the concrete guarded native edge pass

Actual source controls derive the final normalized annotation heap through
all completed pass stages. Public readback applies to the original edge and
the actual returned edge. No generic public guard law or future annotation
invariant is assumed. Original construction supplies finite source execution.
-/
namespace MicroCFTA.SourceEqualityPublicNativeEdge
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityAnnotationHeap SourceEqualityAnnotationLanguage
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityNativeInitial
open SourceEqualityPCSNativeEdge
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "source" => SourceMemoGate.unconstrained
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard

/-- The actual guarded native pass narrows publicly and is publicly exact in its satisfying inherited context. -/
theorem language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : Execution edge inherited before result after) (ready : IdleReady top conjoin before)
    (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge) (closed : MergedColdReaderClosedInputs.ClosedValues edge.children)
    (heap : Heap validGuard before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    Heap validGuard after.machine.heap ∧ ∀ term,
      (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
        InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
      (SourceEqualityPrecheck.Sat term inherited →
        (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
          InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := guardDecidableEq
  have finalHeap := SourceEqualityAnnotationPass.guarded_edge_heap validGuard SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) SourceEqualityConstraintConstructors.top_cached trace ready resident closed heap
  have facts := ready.semantic.ready.semantic.1.normal.facts
  have available := facts.cached.edges edge.entry.key edge resident
  have final := SourceEqualityGuardedEdgeEffects.effects trace ready available closed
  have originalAnnotation := SourceEqualityAnnotationHeap.edge validGuard before.machine.heap heap facts edge resident
  have resultAnnotation := SourceEqualityAnnotationHeap.edge validGuard after.machine.heap finalHeap final.1.semantic.ready.semantic.1.normal.facts result final.2.2.1
  have originalRead := edge_public_eq formulas solver edge originalAnnotation.1 originalAnnotation.2 ambient
  have resultRead := edge_public_eq formulas solver result resultAnnotation.1 resultAnnotation.2 ambient
  refine ⟨finalHeap, ?_⟩
  intro term
  simpa only [originalRead, resultRead] using SourceEqualityPCSNativeEdge.language trace originalAnnotation.1 ready available closed formulas solver ambient term

/-- Original normalized syntax derives finite concrete guarded-edge execution and exact public input/output meaning. -/
theorem source_edges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed validGuard expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Heap validGuard heap ∧
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ inherited,
        Ranges edge inherited (cold width heap) →
          ∃ result after, ∃ trace : Execution edge inherited (cold width heap) result after,
            SourceEqualityGuardedEdgeSource.MemoReads trace ∧ Heap validGuard after.machine.heap ∧ IdleReady top conjoin after ∧
            SourceEqualityRequiredCache.Keeps heap after.machine.heap ∧ InternedEdgeResidency.EdgeResident after.machine.heap result ∧
            MergedColdReaderClosedInputs.ClosedValues result.children ∧
            result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧
            SourceEqualityGuardedEdgeWorker.StableRun
              (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited (cold width heap)) (.ok result) after ∧
            (∃ arrayBound, ∀ work, arrayBound ≤ work → SourceEqualityGuardedEdgeWorker.StableRun
              (fun g e p h c n => SourceEqualityGuardedEdgeWorker.runArray source top conjoin SourceMemoGate.plain top work g e p h c n edge inherited (cold width heap)) (.ok result) after) ∧
            ∀ term,
              (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
                InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
              (SourceEqualityPrecheck.Sat term inherited →
                (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
                  InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  obtain ⟨value, heap, built, physical, _, processed⟩ := SourceEqualityNormalizedEntry.source_edges width expression allowed formulas solver ambient
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built
  have ready := SourceEqualityNativeInitial.ready width top conjoin heap semantic
  refine ⟨value, heap, built, physical, ?_⟩
  intro entry edges depth free original edge member inherited ranges
  have facts := semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges heap facts.linked value available.resident
  rw [original] at resident
  have childAvailable := facts.cached.edges edge.entry.key edge (resident edge member)
  have childClosed : MergedColdReaderClosedInputs.ClosedValues edge.children := by
    rw [original] at available closed
    exact MergedColdReaderClosed.node_children_closed heap facts entry edges depth free available closed edge member
  obtain ⟨result, after, trace, reads, finalReady, symbol, guard, stable, _⟩ :=
    processed entry edges depth free original edge member inherited ranges
  have readback := language trace ready (resident edge member) childClosed physical formulas solver ambient
  have final := SourceEqualityGuardedEdgeEffects.effects trace ready childAvailable childClosed
  exact ⟨result, after, trace, reads, readback.1, finalReady, final.2.1, final.2.2.1, final.2.2.2.2.1, symbol, guard, stable,
    SourceEqualityGuardedEdgeWorkerProofs.array_stable source top conjoin SourceMemoGate.plain top trace, readback.2⟩

end MicroCFTA.SourceEqualityPublicNativeEdge
