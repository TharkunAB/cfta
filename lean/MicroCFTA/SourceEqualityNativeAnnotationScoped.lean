import MicroCFTA.SourceRecursiveIntersectionNativeAnnotationHeap
import MicroCFTA.SourceEqualityNormalizedEntry

/-!
# Normalized annotations through scoped native equality requests

Actual completed native calls retain physical annotation heaps through every
compiled body, memo hit, and completion frame. Concrete source conjunction
and empty-edge construction derive their emitted annotation checks. Closed
public input and output languages therefore have the exact intersection law.
-/
namespace MicroCFTA.SourceEqualityNativeAnnotationScoped
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityAnnotationHeap
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceRecursiveIntersectionAnnotationCode
open SourceObservations SourceSymbolicIndex

/-- Actual checked scoped native requests preserve the physical annotation heap at their complete warm cache scope. -/
theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second))
    {target input result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (trace : Step emptyGuard conjoin target input before result after) (ready : IdleReady emptyGuard conjoin before)
    (targetAvailable : Available before.machine.heap target) (inputAvailable : Available before.machine.heap input)
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases trace with
  | done fuel ranges actual =>
      have nodeReady : NodeReady before.machine ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ :=
        ⟨empty_domain _, targetAvailable, inputAvailable⟩
      have evaluated := SourceRecursiveIntersectionNative.evaluation_of_done emptyGuard conjoin fuel _ before after result actual
      have bounds := evaluated.bounds_of_ranges ranges
      exact bounds.annotation_heap annotation emptyValid conjoinedValid (fun current value => Available current.heap value)
        (by intro value; trivial) (safe_requestNode _ _ _ _ nodeReady) ready.valid
        (annotation_requestNode annotation _ _ _ _ nodeReady) heap

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard

/-- Concrete source native intersection has exact public input and output meanings with derived final annotations. -/
theorem public_product [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {target input result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (trace : Step top conjoin target input before result after) (ready : IdleReady top conjoin before)
    (targetAvailable : Available before.machine.heap target) (inputAvailable : Available before.machine.heap input)
    (targetClosed : target.free = []) (inputClosed : input.free = []) (heap : Heap validGuard before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Heap validGuard after.machine.heap ∧ IdleReady top conjoin after ∧ Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient input term ∧
          InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient target term := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  have finalHeap := step validGuard SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) trace ready targetAvailable inputAvailable heap
  obtain ⟨finalReady, _, resident, closed, product⟩ := trace.verified ready targetAvailable inputAvailable targetClosed inputClosed
    (SourceEqualityPCSGuard.holds formulas solver) (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver)
  refine ⟨finalHeap, finalReady, resident, closed, ?_⟩
  intro ambient term
  have resultAnnotation := available validGuard after.machine.heap finalHeap finalReady.semantic.ready.semantic.1.normal.facts.linked result resident
  have inputAnnotation := available validGuard before.machine.heap heap ready.semantic.ready.semantic.1.normal.facts.linked input inputAvailable
  have targetAnnotation := available validGuard before.machine.heap heap ready.semantic.ready.semantic.1.normal.facts.linked target targetAvailable
  have resultRead := SourceEqualityAnnotationLanguage.public_eq formulas solver result resultAnnotation ambient
  have inputRead := SourceEqualityAnnotationLanguage.public_eq formulas solver input inputAnnotation ambient
  have targetRead := SourceEqualityAnnotationLanguage.public_eq formulas solver target targetAnnotation ambient
  simpa only [resultRead, inputRead, targetRead] using product ambient term

/-- Concrete source scoped requests derive finite complete public intersection from actual reached word checks. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before : NativeState width Symbol Guard) (ready : IdleReady top conjoin before) (heap : Heap validGuard before.machine.heap)
    (target input : Value Symbol Guard) (targetAvailable : Available before.machine.heap target) (inputAvailable : Available before.machine.heap input)
    (targetClosed : target.free = []) (inputClosed : input.free = [])
    (ranges : SourceRecursiveIntersectionNative.WordRanges top conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ result after, Step top conjoin target input before result after ∧ Heap validGuard after.machine.heap ∧ IdleReady top conjoin after ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient input term ∧
          InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient target term := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  obtain ⟨result, after, trace, _⟩ := SourceEqualityNativeScoped.complete top conjoin before ready target input targetAvailable inputAvailable
    targetClosed inputClosed ranges (SourceEqualityPCSGuard.holds formulas solver) (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver)
  exact ⟨result, after, trace, public_product trace ready targetAvailable inputAvailable targetClosed inputClosed heap formulas solver⟩

end MicroCFTA.SourceEqualityNativeAnnotationScoped
