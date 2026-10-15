import MicroCFTA.SourceEqualityGuardedEdgeLanguage
import MicroCFTA.SourceEqualityGuardedEdgeWorkerProofs
import MicroCFTA.SourceEqualityOnePassSource

/-!
# Finite actual guarded-edge reduction from original construction

The actual equality accessor derives own physical records. Complete source
passes retain both gate memo receipts. Literal edge reconstruction derives
the final native validity, exact label, and stable finite source execution.
-/
namespace MicroCFTA.SourceEqualityGuardedEdgeSource
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityClassFoldGraph SourceEqualityNativeInitial SourceEqualityGuardedEdgeGraph
open SourceEqualityGuardedEdgeWorker SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}

/-- The complete edge graph retains the exact actual pass and its two source memo certificates. -/
inductive MemoReads {edge inherited before} :
    {result : EdgeValue Symbol Guard} → {after : NativeState width Symbol Guard} →
      Graph source emptyGuard conjoin clear top edge inherited (before : NativeState width Symbol Guard) result after → Prop where
  | done {payload results middle} (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok payload)
      (pass : SourceEqualityOnePassGraph.Execution source emptyGuard conjoin clear top payload inherited edge.children before (.ok results) middle)
      (reads : SourceEqualityOnePassSource.MemoReads pass) : MemoReads (.done physical pass)

/-- Closed source cache readiness and actual reached ranges derive finite complete original-guard reconstruction. -/
theorem complete (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (node : InternedFreshOrdinaryGateRank.Node Symbol Guard) (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint)
    (stored : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities) (semantic : SemanticReady node.state)
    (available : Values node.state edge.children) (closed : MergedColdReaderClosedInputs.ClosedValues edge.children)
    (ranges : Ranges source emptyGuard conjoin clear top edge inherited (cold width node.state)) :
    ∃ result after, ∃ trace : Graph source emptyGuard conjoin clear top edge inherited (cold width node.state) result after,
      MemoReads trace ∧ IdleReady emptyGuard conjoin after ∧ Keeps node.state after.machine.heap ∧
      InternedEdgeResidency.EdgeResident after.machine.heap result ∧ Values after.machine.heap result.children ∧
      MergedColdReaderClosedInputs.ClosedValues result.children ∧ result.entry.key.symbol = edge.entry.key.symbol ∧
      result.entry.key.constraint = edge.entry.key.constraint ∧
      StableRun (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source emptyGuard conjoin clear top g e p h c n edge inherited (cold width node.state)) (.ok result) after ∧
      ∃ arrayBound, ∀ work, arrayBound ≤ work →
        StableRun (fun g e p h c n => runArray source emptyGuard conjoin clear top work g e p h c n edge inherited (cold width node.state)) (.ok result) after := by
  obtain ⟨payload, physical, _, _⟩ := @SourceEqualityPhysicalPayload.complete Symbol
    (SourceCompactGuards.sourceEqualities edge.entry.key.constraint) (SourceEqualityGuardReadback.source_cached edge.entry.key.constraint stored)
  obtain ⟨results, middle, pass, reads, _, _, _, _, _, _⟩ := SourceEqualityOnePassSource.complete width emptyGuard conjoin clear top
    node edge.children payload inherited semantic available closed (ranges payload physical)
  let trace : Graph source emptyGuard conjoin clear top edge inherited (cold width node.state)
      (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint results) middle.machine.heap).1
      (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint results) middle.machine.heap).2) := .done physical pass
  have checked := SourceEqualityGuardedEdgeEffects.effects trace (SourceEqualityNativeInitial.ready width emptyGuard conjoin node.state semantic) available closed
  exact ⟨_, _, trace, .done physical pass reads, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.1,
    checked.2.2.2.2.2.1, checked.2.2.2.2.2.2, SourceEqualityGuardedEdgeWorkerProofs.stable source emptyGuard conjoin clear top trace,
    SourceEqualityGuardedEdgeWorkerProofs.array_stable source emptyGuard conjoin clear top trace⟩

/-- Original closed construction supplies every edge cache and closed-child premise of finite guarded reduction. -/
theorem source_edges (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (expression : InternedNestedConstruction.Syntax Symbol Guard) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges,
        SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities → ∀ inherited,
          Ranges source emptyGuard conjoin clear top edge inherited (cold width heap) →
          ∃ result after, ∃ trace : Graph source emptyGuard conjoin clear top edge inherited (cold width heap) result after,
            MemoReads trace ∧ IdleReady emptyGuard conjoin after ∧ Keeps heap after.machine.heap ∧
            InternedEdgeResidency.EdgeResident after.machine.heap result ∧ MergedColdReaderClosedInputs.ClosedValues result.children ∧
            result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧
            StableRun (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source emptyGuard conjoin clear top g e p h c n edge inherited (cold width heap)) (.ok result) after := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built
  let node := InternedFreshOrdinaryGateRank.fromCompleted expression value heap built
  refine ⟨value, heap, built, ?_⟩
  intro entry edges depth free original edge member stored inherited ranges
  have facts := semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges heap facts.linked value available.resident
  rw [original] at resident
  have childAvailable := facts.cached.edges edge.entry.key edge (resident edge member)
  have childClosed : MergedColdReaderClosedInputs.ClosedValues edge.children := by
    rw [original] at available closed
    exact MergedColdReaderClosed.node_children_closed heap facts entry edges depth free available closed edge member
  obtain ⟨result, after, trace, reads, ready, keeps, output, _, resultClosed, symbol, guard, stable, _⟩ :=
    complete width emptyGuard conjoin clear top node edge inherited stored semantic childAvailable childClosed ranges
  exact ⟨result, after, trace, reads, ready, keeps, output, resultClosed, symbol, guard, stable⟩

/-- Original closed construction derives stable native edge execution and exact independent language in its inherited context. -/
theorem source_edges_exact (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, acceptsConstraint formulas solver guard term = true)
    (topTrue : ∀ term, acceptsConstraint formulas solver top term = true)
    (conjoined : ∀ first second term, acceptsConstraint formulas solver (conjoin first second) term =
      (acceptsConstraint formulas solver first term && acceptsConstraint formulas solver second term)) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges,
        SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities → ∀ inherited,
          Ranges source emptyGuard conjoin clear top edge inherited (cold width heap) →
          ∃ result after, ∃ trace : Graph source emptyGuard conjoin clear top edge inherited (cold width heap) result after,
            MemoReads trace ∧ IdleReady emptyGuard conjoin after ∧
            result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧
            StableRun (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source emptyGuard conjoin clear top g e p h c n edge inherited (cold width heap)) (.ok result) after ∧
            ∀ term, SourceEqualityPrecheck.Sat term inherited →
              (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
                InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) := by
  obtain ⟨value, heap, built, completed⟩ := source_edges width emptyGuard conjoin clear top expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built
  refine ⟨value, heap, built, ?_⟩
  intro entry edges depth free original edge member stored inherited ranges
  obtain ⟨result, after, trace, reads, ready, _, _, _, symbol, guard, stable⟩ :=
    completed entry edges depth free original edge member stored inherited ranges
  have facts := semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges heap facts.linked value available.resident
  rw [original] at resident
  have childAvailable := facts.cached.edges edge.entry.key edge (resident edge member)
  have childClosed : MergedColdReaderClosedInputs.ClosedValues edge.children := by
    rw [original] at available closed
    exact MergedColdReaderClosed.node_children_closed heap facts entry edges depth free available closed edge member
  refine ⟨result, after, trace, reads, ready, symbol, guard, stable, ?_⟩
  intro term inheritedSat
  exact (SourceEqualityGuardedEdgeLanguage.language trace stored (SourceEqualityNativeInitial.ready width emptyGuard conjoin heap semantic)
    childAvailable childClosed formulas solver ambient clearTrue topTrue conjoined term).2 inheritedSat

end MicroCFTA.SourceEqualityGuardedEdgeSource
