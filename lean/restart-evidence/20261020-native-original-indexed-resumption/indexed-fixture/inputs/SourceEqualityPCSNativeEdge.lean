import MicroCFTA.SourceEqualityPCSGuardedEdge
import MicroCFTA.SourceEqualityGuardedEdgeSource

/-!
# Concrete source guarded-edge exactness at independent PCS semantics

All guard controls are actual source definitions. Source guard structural
comparison decides equality. The proved PCS constructor laws discharge every
generic guard premise. Original construction derives stable finite execution.
-/
namespace MicroCFTA.SourceEqualityPCSNativeEdge
open Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityNativeInitial
open SourceObservations SourceSymbolicIndex SourceEqualityPCSGuard
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- Actual source guard structural comparison decides equality of its complete syntax. -/
def guardDecidableEq : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  fun first second => decidable_of_iff (GuardStructuralOrder.compareGuard first second = .eq) (GuardStructuralOrder.guard_eq first second)

local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := guardDecidableEq

/-- Actual source constraint conjunction uses source structural guard order. -/
noncomputable def conjoin : Guard → Guard → Guard := SourceEqualityConstraintConstructors.conjoin GuardStructuralOrder.le

/-- The complete actual guarded-edge graph fixes each source predicate and constructor control. -/
abbrev Execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :=
  SourceEqualityGuardedEdgeGraph.Graph source top conjoin SourceMemoGate.plain top edge inherited before

/-- Only actual reached primitive native word checks remain explicit at this entry. -/
abbrev Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :=
  SourceEqualityGuardedEdgeGraph.Ranges source top conjoin SourceMemoGate.plain top edge inherited before

/-- Concrete source controls discharge all independent guarded-edge language premises. -/
theorem language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : Execution edge inherited before result after)
    (stored : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap edge.children)
    (closed : MergedColdReaderClosedInputs.ClosedValues edge.children)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    (InternedGuardedLanguage.edgeMeaning (holds formulas solver) ambient result term → InternedGuardedLanguage.edgeMeaning (holds formulas solver) ambient edge term) ∧
      (SourceEqualityPrecheck.Sat term inherited →
        (InternedGuardedLanguage.edgeMeaning (holds formulas solver) ambient result term ↔ InternedGuardedLanguage.edgeMeaning (holds formulas solver) ambient edge term)) :=
  SourceEqualityPCSGuardedEdge.language trace stored ready available closed formulas solver ambient
    (SourceEqualityPCSConstructors.plain_true formulas solver) (SourceEqualityPCSConstructors.top_true formulas solver)
    (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver) term

/-- Original closed source construction gives exact stable native guarded-edge passes with every source control fixed. -/
theorem source_edges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges,
        SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities → ∀ inherited,
          Ranges edge inherited (cold width heap) →
          ∃ result after, ∃ trace : Execution edge inherited (cold width heap) result after,
            SourceEqualityGuardedEdgeSource.MemoReads trace ∧ IdleReady top conjoin after ∧
            result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧
            SourceEqualityGuardedEdgeWorker.StableRun
              (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited (cold width heap)) (.ok result) after ∧
            ∀ term, SourceEqualityPrecheck.Sat term inherited →
              (InternedGuardedLanguage.edgeMeaning (holds formulas solver) ambient result term ↔
                InternedGuardedLanguage.edgeMeaning (holds formulas solver) ambient edge term) := by
  obtain ⟨value, heap, built, completed⟩ := SourceEqualityGuardedEdgeSource.source_edges width top conjoin SourceMemoGate.plain top expression
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
  exact ⟨result, after, trace, reads, ready, symbol, guard, stable, fun term inheritedSat =>
    (language trace stored (SourceEqualityNativeInitial.ready width top conjoin heap semantic)
      childAvailable childClosed formulas solver ambient term).2 inheritedSat⟩

end MicroCFTA.SourceEqualityPCSNativeEdge
