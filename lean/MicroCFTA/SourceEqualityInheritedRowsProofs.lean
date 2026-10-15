import MicroCFTA.SourceEqualityInheritedRows

/-!
# Physical scopes and public language of actual row traversal

The induction composes each concrete guarded native edge pass with its
inherited descendants. Actual cache growth retains earlier rows. No complete
row-preservation law is assumed. The recursive node callback remains explicit.
-/
namespace MicroCFTA.SourceEqualityInheritedRowsProofs
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityRequiredCache
open SourceEqualityAnnotationHeap (Heap)
open SourceEqualityInheritedRows
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard

/-- The ordered row list denotes the union of its complete public guarded edge languages. -/
def meaning (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    List (EdgeValue Symbol Guard) → Term Symbol → Prop
  | [], _ => False
  | edge :: edges, term => InternedGuardedLanguage.edgeMeaning holds ambient edge term ∨ meaning holds ambient edges term

/-- List union and source existential edge selection have the same meaning. -/
theorem meaning_iff (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (edges : List (EdgeValue Symbol Guard)) (term : Term Symbol) :
    meaning holds ambient edges term ↔ ∃ edge ∈ edges, InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  induction edges with
  | nil => simp [meaning]
  | cons edge edges ih => simp only [meaning, ih, List.mem_cons, exists_eq_or_imp]

/-- Each actual complete edge execution derives its full scope and exact contextual public language. -/
theorem edge_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation}
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : SourceEqualityInheritedEdge.Execution call edge inherited before result after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (callback : SourceEqualityInheritedChildrenProofs.Callback validGuard top conjoin
      (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient) call)
    (ready : IdleReady top conjoin before) (resident : EdgeResident before.machine.heap edge)
    (closed : ClosedValues edge.children) (heap : Heap validGuard before.machine.heap) :
    IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ EdgeResident after.machine.heap result ∧
      ClosedValues result.children ∧ Heap validGuard after.machine.heap ∧ ∀ term,
        (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
          InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  have language := trace.language formulas solver ambient callback ready resident closed heap
  cases trace with
  | done narrowed children =>
      have first := SourceEqualityPublicNativeEdge.language narrowed ready resident closed heap formulas solver ambient
      have scope := SourceEqualityGuardedEdgeEffects.effects narrowed ready
        (ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident) closed
      have last := children.verified formulas solver ambient callback scope.1 scope.2.2.1 scope.2.2.2.2.1 first.1
      exact ⟨last.1, scope.2.1.trans last.2.1, last.2.2.1, last.2.2.2.1, language⟩

/-- The complete row graph derives physical scope and exact union meaning from actual individual edge executions. -/
theorem graph_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation}
    {edges results : List (EdgeValue Symbol Guard)} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : Graph call inherited edges before results after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (callback : SourceEqualityInheritedChildrenProofs.Callback validGuard top conjoin
      (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient) call)
    (ready : IdleReady top conjoin before) (resident : Edges before.machine.heap edges)
    (closed : ClosedEdges edges) (heap : Heap validGuard before.machine.heap) :
    IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Edges after.machine.heap results ∧
      ClosedEdges results ∧ Heap validGuard after.machine.heap ∧ ∀ term,
        (meaning (acceptsConstraint formulas solver) ambient results term → meaning (acceptsConstraint formulas solver) ambient edges term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (meaning (acceptsConstraint formulas solver) ambient results term ↔ meaning (acceptsConstraint formulas solver) ambient edges term)) := by
  induction trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, by simp [Edges], by simp [ClosedEdges], heap, fun _ => ⟨id, fun _ => Iff.rfl⟩⟩
  | @cons edge before result middle edges results after first rest ih =>
      have head := edge_verified first formulas solver ambient callback ready (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) heap
      have tail := ih head.1 (fun edge member => edge_grows _ _ head.2.1.growth edge (resident edge (List.mem_cons_of_mem _ member)))
        (fun edge member => closed edge (List.mem_cons_of_mem _ member)) head.2.2.2.2.1
      refine ⟨tail.1, head.2.1.trans tail.2.1, ?_, ?_, tail.2.2.2.2.1, ?_⟩
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact edge_grows _ _ tail.2.1.growth _ head.2.2.1
        · exact tail.2.2.1 edge member
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact head.2.2.2.1
        · exact tail.2.2.2.1 edge member
      · intro term
        have firstLaw := head.2.2.2.2.2 term
        have restLaw := tail.2.2.2.2.2 term
        exact ⟨Or.imp firstLaw.1 restLaw.1, fun satisfied => or_congr (firstLaw.2 satisfied) (restLaw.2 satisfied)⟩

end MicroCFTA.SourceEqualityInheritedRowsProofs
