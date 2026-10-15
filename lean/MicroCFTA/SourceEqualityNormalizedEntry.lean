import MicroCFTA.SourceEqualityAnnotationConstruction

/-!
# Original normalized source annotations at the concrete native edge entry

Original syntax derives the physical annotation heap and exact public input
language. The native edge pass fixes all actual source controls. Its returned
PCS meaning is exactly the original public meaning in a satisfying inherited
context. Public readback of newly constructed outputs needs their annotation
heap preservation, which remains a separate obligation.
-/
namespace MicroCFTA.SourceEqualityNormalizedEntry
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityAnnotationHeap SourceEqualityAnnotationLanguage
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityNativeInitial
open SourceEqualityPCSNativeEdge
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "source" => SourceMemoGate.unconstrained

/-- Every original source edge annotation has the normalized stored-payload representation. -/
def ValidGuard (guard : Guard) : Prop := SourceEqualityGuardReadback.Cached guard.equalities

/-- Original normalized source construction derives full public input readback and concrete stable native edge exactness. -/
theorem source_edges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed ValidGuard expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Heap ValidGuard heap ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value =
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value ∧
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ inherited,
        Ranges edge inherited (cold width heap) →
          ∃ result after, ∃ trace : Execution edge inherited (cold width heap) result after,
            SourceEqualityGuardedEdgeSource.MemoReads trace ∧ IdleReady top conjoin after ∧
            result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧
            SourceEqualityGuardedEdgeWorker.StableRun
              (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited (cold width heap)) (.ok result) after ∧
            ∀ term, SourceEqualityPrecheck.Sat term inherited →
              (InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
                InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) := by
  obtain ⟨value, heap, built, physical, annotated⟩ := SourceEqualityAnnotationConstruction.closed ValidGuard expression allowed
  obtain ⟨other, otherHeap, otherBuilt, processed⟩ := SourceEqualityPCSNativeEdge.source_edges width expression formulas solver ambient
  have same := InternedNestedConstruction.Outcome.done.inj (built.symm.trans otherBuilt)
  cases same.1
  cases same.2
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have available := checked.result value heap built
  have facts : InternedNestedFacts.Facts heap := by simpa only [built, InternedNestedConstruction.Outcome.state] using checked.facts
  refine ⟨value, heap, built, physical, public_eq formulas solver value annotated ambient, ?_⟩
  intro entry edges depth free original edge member inherited ranges
  have resident := InternedEdgeResidency.resident_edges heap facts.linked value available.resident
  rw [original] at resident
  have own := SourceEqualityAnnotationHeap.edge ValidGuard heap physical facts edge (resident edge member)
  obtain ⟨result, after, trace, reads, ready, symbol, guard, stable, exact⟩ :=
    processed entry edges depth free original edge member own.1 inherited ranges
  have readback := edge_public_eq formulas solver edge own.1 own.2 ambient
  refine ⟨result, after, trace, reads, ready, symbol, guard, stable, ?_⟩
  intro term inheritedSat
  simpa only [readback] using exact term inheritedSat

end MicroCFTA.SourceEqualityNormalizedEntry
