import MicroCFTA.SourceEqualityPartialGraph

/-!
# Physical scopes for the actual recursive partial-reduction graph

Each scope retains native readiness, normalized guard annotations, and both
filtered Mu probes. Literal edge construction and both modifyNode branches
derive the next scope from actual effects. No callback law is supplied.
-/
namespace MicroCFTA.SourceEqualityPartialScope
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityRequiredCache
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard

/-- Recursive scopes carry every physical premise needed by the next actual node entry. -/
structure Scope [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (state : NativeState width Symbol Guard) : Prop where
  native : IdleReady top conjoin state
  annotations : SourceEqualityAnnotationHeap.Heap validGuard state.machine.heap
  probes : InternedFreshOrdinaryProbeHeap.Heap state.machine.heap

/-- The actual local native pass derives its returned scope and complete row residency. -/
theorem Scope.narrow [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (scope : Scope before) (trace : SourceEqualityPCSNativeEdge.Execution edge inherited before result after)
    (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge) (closed : MergedColdReaderClosedInputs.ClosedValues edge.children)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol) :
    Scope after ∧ Keeps before.machine.heap after.machine.heap ∧ InternedEdgeResidency.EdgeResident after.machine.heap result ∧
      MergedColdReaderClosedInputs.ClosedValues result.children ∧ ∀ term,
        (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
          InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  have physical := SourceEqualityGuardedEdgeEffects.effects trace scope.native (facts.cached.edges edge.entry.key edge resident) closed
  have language := SourceEqualityPublicNativeEdge.language trace scope.native resident closed scope.annotations formulas solver ambient
  have probes := SourceEqualityProbePass.guarded_edge_heap trace scope.native resident closed scope.probes
  exact ⟨⟨physical.1, language.1, probes⟩, physical.2.1, physical.2.2.1, physical.2.2.2.2.1, language.2⟩

/-- Literal source edge allocation derives both physical heaps and actual returned child fields. -/
theorem Scope.edge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (before : NativeState width Symbol Guard)
    (scope : Scope before) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (valid : validGuard guard) (available : Values before.machine.heap values) :
    let built := run (makeEdge symbol guard values) before.machine.heap
    Scope (advanceHeap before built.2) ∧ Keeps before.machine.heap built.2 ∧ InternedEdgeResidency.EdgeResident built.2 built.1 ∧
      built.1.children = values := by
  have built := SourceEqualityRequiredCache.edge symbol guard values before.machine.heap scope.native.semantic.ready available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard values before.machine.heap scope.native.semantic available
  have annotations := SourceEqualityAnnotationHeap.run validGuard _ (SourceEqualityAnnotationHeap.makeEdge validGuard symbol guard values valid)
    before.machine.heap scope.annotations
  have probes := InternedFreshOrdinaryProbeHeap.edge symbol guard values before.machine.heap scope.probes
  exact ⟨⟨scope.native.advance _ built.1 semantic, annotations, probes⟩, built⟩

/-- Both literal node reconstruction branches retain the probe invariant at their returned heap. -/
theorem modify_probes [DecidableEq (EdgeKey Symbol Guard)] (original : Value Symbol Guard)
    (oldRows newRows : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard)
    (heap : InternedFreshOrdinaryProbeHeap.Heap before.machine.heap) :
    InternedFreshOrdinaryProbeHeap.Heap (SourceEqualityPartialNodeRebuild.modify original oldRows newRows before).2.machine.heap := by
  unfold SourceEqualityPartialNodeRebuild.modify
  split
  · exact heap
  · exact InternedFreshOrdinaryProbeHeap.node newRows before.machine.heap heap

/-- The actual modifyNode fast path and node request derive complete scope and exact public row-union meaning. -/
theorem Scope.modify [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : NativeState width Symbol Guard)
    (scope : Scope before) (available : Available before.machine.heap (.node entry oldRows depth free))
    (closed : (Value.node entry oldRows depth free).free = []) (resident : Edges before.machine.heap newRows) (newClosed : ClosedEdges newRows)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    let built := SourceEqualityPartialNodeRebuild.modify (.node entry oldRows depth free) oldRows newRows before
    Scope built.2 ∧ Keeps before.machine.heap built.2.machine.heap ∧ Available built.2.machine.heap built.1 ∧ built.1.free = [] ∧
      ∀ term, InternedGuardedLanguage.meaning holds ambient built.1 term ↔ ∃ edge ∈ newRows, InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  have built := SourceEqualityPartialNodeRebuild.verified validGuard top conjoin entry oldRows newRows depth free before scope.native
    available closed resident newClosed scope.annotations holds ambient
  exact ⟨⟨built.1, built.2.2.2.2.1, modify_probes _ oldRows newRows before scope.probes⟩, built.2.1, built.2.2.1, built.2.2.2.1, built.2.2.2.2.2⟩

end MicroCFTA.SourceEqualityPartialScope
