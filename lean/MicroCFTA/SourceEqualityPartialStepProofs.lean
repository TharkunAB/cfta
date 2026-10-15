import MicroCFTA.SourceEqualityPartialWorker

/-!
# Scoped proof of one actual outer partial-reduction step

Actual ordinary rows supply their public language and physical effects.
Literal node reconstruction closes that branch. Mu uses the proved cached
probe hit and smart cleanup. Concrete reached word checks and filtered Mu
probes remain explicit. The recursive callback law is still an induction
premise; this file does not prove general recursive completion.
-/
namespace MicroCFTA.SourceEqualityPartialStepProofs
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityRequiredCache
open SourceEqualityAnnotationHeap (Heap)
open SourceEqualityPartialWorker
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard

/-- Advancing to the identical constructor heap leaves every native field unchanged. -/
theorem advance_self (before : NativeState width Symbol Guard) : advanceHeap before before.machine.heap = before := rfl

/-- Closed coherent ordinary nodes retain closed children in every actual stored row. -/
theorem closed_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before : NativeState width Symbol Guard) (ready : IdleReady top conjoin before)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available before.machine.heap (.node entry edges depth free)) (closed : (Value.node entry edges depth free).free = []) : ClosedEdges edges := by
  have names := InternedNormalizationFree.node_free before.machine.heap ready.semantic.ready.semantic.1.normal.facts.coherent entry edges depth free available.resident
  intro edge included child member
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name named
  have parent := (childFree_member _ name).mpr ⟨child, List.mem_flatMap.mpr ⟨edge, included, member⟩, named⟩
  rw [← names] at parent
  change free = [] at closed
  rw [closed] at parent
  cases parent

/-- The concrete completed ordinary branch derives scope, narrowing, and exact inherited public meaning. -/
theorem ordinary [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width)
    (inherited : SourceEqualityPrecheck.Constraint) (entry : Interned InternedBinderProtocol.NodeKey)
    (edges results : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before middle : NativeState width Symbol Guard) (trace : SourceEqualityInheritedRows.Graph call inherited edges before results middle)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (callback : SourceEqualityInheritedChildrenProofs.Callback validGuard top conjoin
      (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient) call)
    (ready : IdleReady top conjoin before) (available : Available before.machine.heap (.node entry edges depth free))
    (closed : (Value.node entry edges depth free).free = []) (heap : Heap validGuard before.machine.heap) :
    let built := SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle
    IdleReady top conjoin built.2 ∧ Keeps before.machine.heap built.2.machine.heap ∧ Available built.2.machine.heap built.1 ∧
      built.1.free = [] ∧ Heap validGuard built.2.machine.heap ∧ ∀ term,
        (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient built.1 term →
          InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient (.node entry edges depth free) term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient built.1 term ↔
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient (.node entry edges depth free) term)) := by
  have rows := SourceEqualityInheritedRowsProofs.graph_verified trace formulas solver ambient callback ready
    (resident_edges _ ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident) (closed_rows before ready entry edges depth free available closed) heap
  have built := SourceEqualityPartialNodeRebuild.verified validGuard top conjoin entry edges results depth free middle rows.1
    (rows.2.1.available _ available) closed rows.2.2.1 rows.2.2.2.1 rows.2.2.2.2.1 (acceptsConstraint formulas solver) ambient
  refine ⟨built.1, rows.2.1.trans built.2.1, built.2.2.1, built.2.2.2.1, built.2.2.2.2.1, ?_⟩
  intro term
  have output := (built.2.2.2.2.2 term).trans (SourceEqualityInheritedRowsProofs.meaning_iff (acceptsConstraint formulas solver) ambient results term).symm
  have input := (SourceEqualityPartialNodeRebuild.node_meaning (acceptsConstraint formulas solver) ambient entry edges depth free term).trans
    (SourceEqualityInheritedRowsProofs.meaning_iff (acceptsConstraint formulas solver) ambient edges term).symm
  have law := rows.2.2.2.2.2 term
  exact ⟨fun accepted => input.mpr (law.1 (output.mp accepted)), fun satisfied => output.trans ((law.2 satisfied).trans input.symm)⟩

/-- One source step checks only its actual Mu probes or actual reached row word ranges. -/
def Checks [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width)
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard) (before : NativeState width Symbol Guard) : Prop :=
  match value with
  | .mu _ _ depth ordinary => InternedFreshOrdinaryProbeFilter.Clean depth ordinary
  | .node _ edges _ _ => SourceEqualityInheritedRows.Ranges call g e p h c n inherited edges before
  | _ => True

/-- Successful outer steps derive the local callback conclusion from concrete checks and the smaller-call premise. -/
theorem step_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width)
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard) (before : NativeState width Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (callback : SourceEqualityInheritedChildrenProofs.Callback validGuard top conjoin
      (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient) call)
    (checks : Checks call g e p h c n inherited value before)
    (ready : IdleReady top conjoin before) (available : Available before.machine.heap value) (closed : value.free = [])
    (heap : Heap validGuard before.machine.heap) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : step call g e p h c n inherited value before = .done (.ok result) after) :
    IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      Heap validGuard after.machine.heap ∧ ∀ term,
        (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term →
          InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term)) := by
  cases value with
  | empty | union =>
      cases done
      exact ⟨ready, pure_keeps _ ready.semantic.ready, available, closed, heap, fun _ => ⟨id, fun _ => Iff.rfl⟩⟩
  | reference => simp only [step] at done; cases done
  | mu entry body depth ordinary =>
      have proof := SourceEqualityMuReconstruction.verified entry body depth ordinary before.machine.heap
        ready.semantic.ready.semantic.1.normal.facts.coherent available checks (acceptsConstraint formulas solver) ambient
      simp only [step, proof.1, advance_self, SourceEqualityInheritedChildren.Result.done.injEq, Except.ok.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact ⟨ready, pure_keeps _ ready.semantic.ready, proof.2.1, proof.2.2.1.trans closed, heap,
        fun term => ⟨fun accepted => (iff_of_eq (congrFun proof.2.2.2 term)).mp accepted,
          fun _ => iff_of_eq (congrFun proof.2.2.2 term)⟩⟩
  | node entry edges depth free =>
      cases actual : SourceEqualityInheritedRows.walk call g e p h c n inherited edges before with
      | incomplete => simp only [step, actual] at done; cases done
      | done answer middle =>
          cases answer with
          | error => simp only [step, actual] at done; cases done
          | ok results =>
              have graph := SourceEqualityInheritedRows.graph g e p h c n checks actual
              have proof := ordinary call inherited entry edges results depth free before middle graph formulas solver ambient callback ready available closed heap
              simp only [step, actual, SourceEqualityInheritedChildren.Result.done.injEq, Except.ok.injEq] at done
              rcases done with ⟨rfl, rfl⟩
              exact proof

/-- Original closed source construction derives the exact bounded Mu branch from its actual stored record. -/
theorem constructed_mu [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard) (root : Value Symbol Guard)
    (state : State Symbol Guard) (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done root state)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : state.nodeRecords entry.key = some (.mu entry body depth ordinary))
    (g e p h c n fuel : Nat) (inherited : SourceEqualityPrecheck.Constraint)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    SourceEqualityPartialWorker.run g e p h c n (fuel + 1) inherited (.mu entry body depth ordinary)
        (SourceEqualityNativeInitial.cold width state) =
      .done (.ok (cleanup (.mu entry body depth ordinary))) (SourceEqualityNativeInitial.cold width state) ∧
      Available state (cleanup (.mu entry body depth ordinary)) ∧
      InternedGuardedLanguage.meaning holds ambient (cleanup (.mu entry body depth ordinary)) =
        InternedGuardedLanguage.meaning holds ambient (.mu entry body depth ordinary) := by
  have facts : InternedNestedFacts.Facts state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using (InternedFreshOrdinaryFacts.closed_verified expression).facts
  have available := facts.cached.nodes entry.key _ stored
  have clean := InternedFreshOrdinaryProbeFilter.constructed expression root state built entry body depth ordinary available
  have actual := SourceEqualityMuReconstruction.verified entry body depth ordinary state facts.coherent available clean holds ambient
  refine ⟨?_, actual.2.1, actual.2.2.2⟩
  simp only [SourceEqualityPartialWorker.run, step, SourceEqualityNativeInitial.cold, SourceRecursiveIntersectionThunks.initial,
    actual.1]
  rfl

end MicroCFTA.SourceEqualityPartialStepProofs
