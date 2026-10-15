import MicroCFTA.SourceEqualityPartialConstraintClosure
import MicroCFTA.SourceEqualityConstraintOrigins
import MicroCFTA.SourceEqualityPartialMemoSource

/-!
# Original constraint origins after checked recursive public execution

Original syntax supplies every literal guard, including stored binder
bodies. Actual checked success derives its outer graph. Constraint closure
then follows actual recursive effects. The result retains exact language,
both source gate memo receipts, and stable replay. Successful execution is
an explicit premise. These origin derivations do not prove termination.
-/
namespace MicroCFTA.SourceEqualityPartialConstraintOrigins
open InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphRuns SourceEqualityPartialMemoGraph
open SourceEqualityAnnotationHeap (Heap)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityConstraintOrigins (Derived guards)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A completed outer graph derives literal, Top, and conjunction origins from its actual initial heap. -/
theorem node {width : Nat} (literals : List Guard) {inherited value result} {before after : NativeState width Symbol Guard}
    (trace : ReduceNode inherited value before result after) (scope : Scope before)
    (available : Available before.machine.heap value) (closed : value.free = [])
    (origins : Heap (Derived literals top conjoin) before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    Heap (Derived literals top conjoin) after.machine.heap ∧ Annotated (Derived literals top conjoin) result := by
  have finalHeap := SourceEqualityPartialConstraintClosure.node formulas solver ambient (Derived literals top conjoin)
    Derived.top (fun _ _ first second => .conjunction first second) trace scope available closed origins
  have final := SourceEqualityPartialGraphProofs.node formulas solver ambient trace scope available closed
  exact ⟨finalHeap, SourceEqualityAnnotationHeap.available _ _ finalHeap
    final.1.native.semantic.ready.semantic.1.normal.facts.linked result final.2.2.1⟩

/-- Checked public success retains original constraint origins, actual source memo receipts, exact language, and stable replay. -/
theorem public_exact {width : Nat} (literals : List Guard) (g e p h c n fuel : Nat)
    {value result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (plan : SourceEqualityPartialChecks.Checked g e p h c n fuel (some []) value before)
    (done : SourceEqualityPartialWorker.run g e p h c n fuel (some []) value before = .done (.ok result) after)
    (scope : Scope before) (available : Available before.machine.heap value) (closed : value.free = [])
    (origins : Heap (Derived literals top conjoin) before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ trace : ReduceNode (some []) value before result after,
      Heap (Derived literals top conjoin) after.machine.heap ∧ Annotated (Derived literals top conjoin) result ∧ NodeReads trace ∧
      Scope after ∧ SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧ NodeRun (some []) value before result after ∧
      ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  obtain ⟨trace, reads, final⟩ := SourceEqualityPartialMemoSource.public_exact g e p h c n fuel plan done
    scope available closed formulas solver ambient
  have derived := node literals trace scope available closed origins formulas solver ambient
  exact ⟨trace, derived.1, derived.2, reads, final⟩

/-- Original closed normalized syntax derives constraint origins for every actual checked successful public return. -/
theorem closed (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (normalized : SourceEqualityAnnotationConstruction.Allowed SourceEqualityNormalizedEntry.ValidGuard expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Scope (cold width heap) ∧ Heap (Derived (guards expression) top conjoin) heap ∧ Available heap value ∧ value.free = [] ∧
      ∀ g e p h c n fuel result after,
        SourceEqualityPartialChecks.Checked g e p h c n fuel (some []) value (cold width heap) →
        SourceEqualityPartialWorker.run g e p h c n fuel (some []) value (cold width heap) = .done (.ok result) after →
        ∃ trace : ReduceNode (some []) value (cold width heap) result after,
          Heap (Derived (guards expression) top conjoin) after.machine.heap ∧
          Annotated (Derived (guards expression) top conjoin) result ∧ NodeReads trace ∧ Scope after ∧
          SourceEqualityRequiredCache.Keeps heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
          NodeRun (some []) value (cold width heap) result after ∧
          ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  obtain ⟨value, heap, built, scope, origins, available, valueClosed⟩ :=
    SourceEqualityConstraintOrigins.closed width expression normalized
  exact ⟨value, heap, built, scope, origins, available, valueClosed,
    fun g e p h c n fuel _ _ plan done =>
      public_exact (guards expression) g e p h c n fuel plan done scope available valueClosed origins formulas solver ambient⟩

end MicroCFTA.SourceEqualityPartialConstraintOrigins
