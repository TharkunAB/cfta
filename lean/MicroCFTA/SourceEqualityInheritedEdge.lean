import MicroCFTA.SourceEqualityInheritedChildrenProofs

/-!
# Actual inherited child continuation after guarded edge narrowing

The graph reads the complete source guard payload, combines inherited and
local constraints, traverses children at their actual indexes, and performs
the source equal-arity edge request. The concrete native guarded-edge theorem
supplies the preceding local narrowing step. The recursive node callback law
remains the induction obligation of the outer reducePartially caller.
-/
namespace MicroCFTA.SourceEqualityInheritedEdge
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityAnnotationHeap (Heap)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard

/-- The actual reduceChildren continuation retains source payload, child, and constructor receipts. -/
inductive Graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation)
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :
    EdgeValue Symbol Guard → NativeState width Symbol Guard → Prop where
  | done (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok own)
      (combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload)
      (children : SourceEqualityInheritedChildren.Graph call payload edge.children before values middle) :
      Graph call edge inherited before (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap).1
        (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap).2)

/-- Full source edge processing first narrows locally, then runs its actual inherited child continuation. -/
inductive Execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation)
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :
    EdgeValue Symbol Guard → NativeState width Symbol Guard → Prop where
  | done (narrowed : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowedEdge middle)
      (children : Graph call narrowedEdge inherited middle result after) : Execution call edge inherited before result after

/-- Actual inherited edge continuation derives scope, annotations, original labels, and exact contextual public meaning. -/
theorem Graph.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation}
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : Graph call edge inherited before result after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (callback : SourceEqualityInheritedChildrenProofs.Callback validGuard top conjoin
      (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient) call)
    (ready : IdleReady top conjoin before) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (closed : ClosedValues edge.children) (heap : Heap validGuard before.machine.heap) :
    IdleReady top conjoin after ∧ SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      InternedEdgeResidency.EdgeResident after.machine.heap result ∧ ClosedValues result.children ∧ Heap validGuard after.machine.heap ∧
      result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧ ∀ term,
        (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
          InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  cases trace with
  | @done own payload values middle physical combined children =>
      have facts := ready.semantic.ready.semantic.1.normal.facts
      have stored := heap edge.entry.key edge resident
      obtain ⟨actualOwn, actual, _, acceptedOwn⟩ := SourceEqualityInheritedPayload.own_complete formulas solver edge.entry.key.constraint stored
      have same := Except.ok.inj (actual.symm.trans physical)
      subst actualOwn
      have combinedFacts : SourceEqualityDescend.WellFormed payload ∧ ∀ term : Term Symbol, SourceEqualityPrecheck.Sat term payload ↔
          SourceEqualityPrecheck.Sat term inherited ∧ SourceEqualityPrecheck.Sat term own := SourceEqualityInheritedPayload.combine_exact combined
      have checked := SourceEqualityInheritedChildrenProofs.graph_verified validGuard top conjoin (acceptsConstraint formulas solver) ambient call callback children
        ready (facts.cached.edges edge.entry.key edge resident) closed heap combinedFacts.1
      have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint _ _ checked.1.semantic.ready checked.2.2.1
      have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint _ _ checked.1.semantic checked.2.2.1
      have fields := MergedPhysicalGroupEdges.makeEdge_fields _ checked.1.semantic.ready.semantic.1.normal.facts
        edge.entry.key.symbol edge.entry.key.constraint _ checked.2.2.1
      have finalHeap := SourceEqualityAnnotationHeap.run validGuard _
        (SourceEqualityAnnotationHeap.makeEdge validGuard edge.entry.key.symbol edge.entry.key.constraint values stored) middle.machine.heap checked.2.2.2.2.1
      refine ⟨checked.1.advance _ built.1 semantic, checked.2.1.trans built.1, built.2.1, ?_, finalHeap, fields.1, fields.2.1, ?_⟩
      · rw [built.2.2]
        exact checked.2.2.2.1
      · intro term
        rw [InternedGuardedLanguage.edgeMeaning_all, InternedGuardedLanguage.edgeMeaning_all]
        simp only [MergedColdInterpretation.EdgeMeaning, fields.1, fields.2.1, fields.2.2]
        constructor
        · rintro ⟨terms, shape, runs, guard⟩
          exact ⟨terms, shape, (checked.2.2.2.2.2 edge.entry.key.symbol terms).1 runs, guard⟩
        · intro inheritedSat
          constructor
          · rintro ⟨terms, shape, runs, guard⟩
            exact ⟨terms, shape, (checked.2.2.2.2.2 edge.entry.key.symbol terms).1 runs, guard⟩
          · rintro ⟨terms, shape, runs, guard⟩
            have parentSat := (combinedFacts.2 term).mpr ⟨inheritedSat, acceptedOwn term guard⟩
            exact ⟨terms, shape, ((checked.2.2.2.2.2 edge.entry.key.symbol terms).2 (shape ▸ parentSat)).mpr runs, guard⟩

/-- Concrete native local narrowing and actual inherited child processing compose without generic edge-language laws. -/
theorem Execution.language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation}
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : Execution call edge inherited before result after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (callback : SourceEqualityInheritedChildrenProofs.Callback validGuard top conjoin
      (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient) call)
    (ready : IdleReady top conjoin before) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (closed : ClosedValues edge.children) (heap : Heap validGuard before.machine.heap) :
    Heap validGuard after.machine.heap ∧ ∀ term,
      (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
        InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
      (SourceEqualityPrecheck.Sat term inherited →
        (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
          InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  cases trace with
  | done narrowed children =>
      have first := SourceEqualityPublicNativeEdge.language narrowed ready resident closed heap formulas solver ambient
      have scope := SourceEqualityGuardedEdgeEffects.effects narrowed ready
        (ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident) closed
      have last := children.verified formulas solver ambient callback scope.1 scope.2.2.1 scope.2.2.2.2.1 first.1
      refine ⟨last.2.2.2.2.1, ?_⟩
      intro term
      have final := last.2.2.2.2.2.2.2 term
      exact ⟨fun accepted => (first.2 term).1 (final.1 accepted), fun satisfied => (final.2 satisfied).trans ((first.2 term).2 satisfied)⟩

end MicroCFTA.SourceEqualityInheritedEdge
