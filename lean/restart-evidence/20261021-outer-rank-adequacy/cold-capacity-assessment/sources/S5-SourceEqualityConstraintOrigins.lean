import MicroCFTA.SourceEqualityConstraintPassClosure
import MicroCFTA.SourceEqualityWarmNativeEdge

/-!
# Original source origins of every guarded native prefix constraint

The finite literal inventory includes guards in every stored binder body.
Original construction derives the initial constraint heap. Each actual
warm native prefix emits only a literal guard, Top, or a conjunction of
previously derived guards. This is origin evidence, not a decreasing measure.
-/
namespace MicroCFTA.SourceEqualityConstraintOrigins
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceEqualityAnnotationConstruction SourceEqualityAnnotationHeap

/-- A physical constraint comes from an original literal, source Top, or actual source conjunction. -/
inductive Derived (literals : List Guard) (top : Guard) (conjoin : Guard → Guard → Guard) : Guard → Prop where
  | literal {guard : Guard} (member : guard ∈ literals) : Derived literals top conjoin guard
  | top : Derived literals top conjoin top
  | conjunction (first : Derived literals top conjoin left) (second : Derived literals top conjoin right) :
      Derived literals top conjoin (conjoin left right)

mutual
/-- Read every complete literal guard, including guards inside raw and smart binders. -/
def guards : Syntax Symbol Guard → List Guard
  | .empty | .var _ => []
  | .node edges => edgeGuards edges
  | .union members => childGuards members
  | .binder _ body => guards body

/-- Retain literal guard occurrences in original child order. -/
def childGuards : List (Syntax Symbol Guard) → List Guard
  | [] => []
  | first :: rest => guards first ++ childGuards rest

/-- Include each row guard before the complete literal guards of its children and tail. -/
def edgeGuards : List (EdgeSyntax Symbol Guard) → List Guard
  | [] => []
  | .mk _ guard children :: rest => guard :: (childGuards children ++ edgeGuards rest)
end

mutual
/-- Literal inventory membership derives every original source annotation check. -/
theorem allowed (annotation : Guard → Prop) (expression : Syntax Symbol Guard)
    (checked : ∀ guard ∈ guards expression, annotation guard) : Allowed annotation expression := by
  cases expression with
  | empty | var => simp only [Allowed]
  | node edges => simpa only [Allowed] using edges_allowed annotation edges checked
  | union members => simpa only [Allowed] using children_allowed annotation members checked
  | binder smart body => simpa only [Allowed] using allowed annotation body checked
termination_by sizeOf expression

/-- Each child uses its original sublist of the finite literal inventory. -/
theorem children_allowed (annotation : Guard → Prop) (expressions : List (Syntax Symbol Guard))
    (checked : ∀ guard ∈ childGuards expressions, annotation guard) : ManyAllowed annotation expressions := by
  cases expressions with
  | nil => simp only [ManyAllowed]
  | cons first rest =>
      simp only [ManyAllowed]
      simp only [childGuards] at checked
      exact ⟨allowed annotation first (fun guard member => checked guard (List.mem_append_left _ member)),
        children_allowed annotation rest (fun guard member => checked guard (List.mem_append_right _ member))⟩
termination_by sizeOf expressions

/-- Row and child inventory membership retain the actual complete guard of every literal edge. -/
theorem edges_allowed (annotation : Guard → Prop) (expressions : List (EdgeSyntax Symbol Guard))
    (checked : ∀ guard ∈ edgeGuards expressions, annotation guard) : EdgesAllowed annotation expressions := by
  cases expressions with
  | nil => simp only [EdgesAllowed]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [EdgesAllowed]
          simp only [edgeGuards] at checked
          exact ⟨checked guard List.mem_cons_self,
            children_allowed annotation children (fun other member => checked other
              (List.mem_cons_of_mem _ (List.mem_append_left _ member))),
            edges_allowed annotation rest (fun other member => checked other
              (List.mem_cons_of_mem _ (List.mem_append_right _ member)))⟩
termination_by sizeOf expressions
end

/-- Actual source construction derives constraint origins from its finite original literal inventory. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (top : Guard) (conjoin : Guard → Guard → Guard)
    (expression : Syntax Symbol Guard) (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    Heap (Derived (guards expression) top conjoin) heap := by
  have literalChecks : Allowed (Derived (guards expression) top conjoin) expression :=
    allowed _ expression (fun _ member => .literal member)
  simpa only [built, Outcome.state] using SourceEqualityAnnotationConstruction.build
    (Derived (guards expression) top conjoin) expression literalChecks [] empty (empty_heap _)

open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityPartialScope
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Original closed normalized construction supplies recursive scope, closed availability, and literal constraint origins. -/
theorem closed (width : Nat) (expression : Syntax Symbol Guard)
    (normalized : Allowed SourceEqualityNormalizedEntry.ValidGuard expression) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Scope (SourceEqualityNativeInitial.cold width heap) ∧ Heap (Derived (guards expression) top conjoin) heap ∧
      Available heap value ∧ value.free = [] := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have initial := SourceEqualityPartialSource.constructed width expression normalized value heap built
  exact ⟨value, heap, built, initial.1, constructed top conjoin expression value heap built, initial.2⟩

/-- Finite actual guarded prefixes retain only literal, Top, and conjunction-derived constraints at their returned warm scope. -/
theorem complete (literals : List Guard) (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint)
    (before : NativeState width Symbol Guard) (scope : Scope before)
    (origins : Heap (Derived literals top conjoin) before.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (closed : MergedColdReaderClosedInputs.ClosedValues edge.children)
    (ranges : SourceEqualityPCSNativeEdge.Ranges edge inherited before)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ result after, ∃ trace : SourceEqualityPCSNativeEdge.Execution edge inherited before result after,
      Heap (Derived literals top conjoin) after.machine.heap ∧ SourceEqualityClosedMemoReads.EdgeReads trace ∧ Scope after ∧
      SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      InternedEdgeResidency.EdgeResident after.machine.heap result ∧ MergedColdReaderClosedInputs.ClosedValues result.children ∧
      SourceEqualityGuardedEdgeWorker.StableRun
        (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top
          g e p h c n edge inherited before) (.ok result) after ∧
      ∀ term,
        (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term →
          InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  obtain ⟨result, after, trace, reads, finalScope, keeps, finalResident, resultClosed, _, _, stable, _, language⟩ :=
    SourceEqualityWarmNativeEdge.complete edge inherited before scope resident closed ranges formulas solver ambient
  have finalOrigins := SourceEqualityConstraintPassClosure.guarded_edge_heap (Derived literals top conjoin)
    Derived.top (fun _ _ first second => .conjunction first second) Derived.top trace scope.native resident closed origins
  exact ⟨result, after, trace, finalOrigins, reads, finalScope, keeps, finalResident, resultClosed, stable, language⟩

end MicroCFTA.SourceEqualityConstraintOrigins
