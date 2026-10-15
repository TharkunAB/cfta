import MicroCFTA.SourceEqualityWarmOnePass

/-!
# Finite exact guarded edges at arbitrary closed warm scopes

The current annotation heap derives physical own payload readback. Finite
closed selection, required paths, and the native fold construct the actual
guarded edge prefix. Literal interning derives its returned scope. No
successful prefix, original construction, or future scope is supplied.
-/
namespace MicroCFTA.SourceEqualityWarmNativeEdge
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialScope SourceEqualityPCSNativeEdge
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "source" => SourceMemoGate.unconstrained
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual physical annotation and local word checks derive finite edge execution at the current warm scope. -/
theorem graph (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint)
    (before : NativeState width Symbol Guard) (scope : Scope before)
    (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge) (closed : ClosedValues edge.children)
    (ranges : SourceEqualityPCSNativeEdge.Ranges edge inherited before) :
    ∃ result after, Execution edge inherited before result after := by
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  have stored := scope.annotations edge.entry.key edge resident
  obtain ⟨payload, physical, _, _⟩ := @SourceEqualityPhysicalPayload.complete Symbol
    (SourceCompactGuards.sourceEqualities edge.entry.key.constraint)
      (SourceEqualityGuardReadback.source_cached edge.entry.key.constraint stored)
  have actual : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok payload := physical
  obtain ⟨results, middle, pass⟩ := SourceEqualityWarmOnePass.graph payload inherited edge.children before scope.native
    (facts.cached.edges _ _ resident) closed (ranges payload actual)
  exact ⟨_, _, .done actual pass⟩

/-- Every checked closed warm edge derives both source memo receipts, full recursive scope, stable replay, and exact public contextual language. -/
theorem complete (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint)
    (before : NativeState width Symbol Guard) (scope : Scope before)
    (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge) (closed : ClosedValues edge.children)
    (ranges : SourceEqualityPCSNativeEdge.Ranges edge inherited before)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ result after, ∃ trace : Execution edge inherited before result after,
      SourceEqualityClosedMemoReads.EdgeReads trace ∧ Scope after ∧
      SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      InternedEdgeResidency.EdgeResident after.machine.heap result ∧ ClosedValues result.children ∧
      result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧
      SourceEqualityGuardedEdgeWorker.StableRun
        (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top
          g e p h c n edge inherited before) (.ok result) after ∧
      (∃ arrayBound, ∀ work, arrayBound ≤ work → SourceEqualityGuardedEdgeWorker.StableRun
        (fun g e p h c n => SourceEqualityGuardedEdgeWorker.runArray source top conjoin SourceMemoGate.plain top
          work g e p h c n edge inherited before) (.ok result) after) ∧
      ∀ term,
        (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
          InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  obtain ⟨result, after, trace⟩ := graph edge inherited before scope resident closed ranges
  have effects := scope.narrow trace resident closed formulas solver ambient
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  have fields := SourceEqualityGuardedEdgeEffects.effects trace scope.native (facts.cached.edges _ _ resident) closed
  exact ⟨result, after, trace, SourceEqualityClosedMemoReads.edge trace facts resident closed,
    effects.1, effects.2.1, effects.2.2.1, effects.2.2.2.1, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2,
    SourceEqualityGuardedEdgeWorkerProofs.stable source top conjoin SourceMemoGate.plain top trace,
    SourceEqualityGuardedEdgeWorkerProofs.array_stable source top conjoin SourceMemoGate.plain top trace, effects.2.2.2.2⟩

end MicroCFTA.SourceEqualityWarmNativeEdge
