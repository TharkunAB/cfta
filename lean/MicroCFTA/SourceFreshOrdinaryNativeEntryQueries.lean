import MicroCFTA.SourceFreshOrdinaryNativeEntryReadback
import MicroCFTA.SourceSizedApiLaws

/-!
# Exact public Sized laws after actual native entry control

Every successful reference or native result has finite exact size classes,
size-major order, and both distinct-term inverse laws. Physical root checks,
actual cold traversal, and native scan correspondence derive the result.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeEntry
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks

variable {bits : Nat} {Formula Key : Type} [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (value : Value (Label Formula) (Constraint Formula))

local notation "N" => SourceRecursiveIntersectionThunks.State (bits + 2) (Label Formula) (Constraint Formula)
local notation "Api" => SourceSizedDispatcher.Api (Label Formula)

/-- Successful physical-root reference results satisfy every exact public Sized query law. -/
theorem Reference.exact_queries (state : N) (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (available : Available state.machine.heap value) (result : Except SourceCyclicAutomaton.Error Api) (api : Api)
    (actual : Reference formulas solver order value state result) (success : result = .ok api)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    SourceSizedApiLaws.Exact api (fun term => InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) := by
  obtain ⟨State, rows, root, rfl, language⟩ := Reference.success_readback formulas solver order value emptyGuard conjoin
    state ready available result api actual success ambient
  exact SourceSizedApiLaws.reference rows root _ language

/-- Every actual successful public native entry satisfies the same complete reference query specification. -/
theorem Execution.exact_queries (state : N) (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (available : Available state.machine.heap value) (ranges : Ranges emptyGuard conjoin order value state)
    (result : Except SourceCyclicAutomaton.Error Api) (after : N) (api : Api)
    (actual : Execution emptyGuard conjoin formulas solver order value state result after) (success : result = .ok api)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    SourceSizedApiLaws.Exact api (fun term => InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) := by
  have reference := (execution_correct emptyGuard conjoin formulas solver order value state ready available ranges result after actual).2
  exact Reference.exact_queries emptyGuard conjoin formulas solver order value state ready available result api reference success ambient

/-- Finite actual public execution returns the exact source error or a complete exact Sized query record. -/
theorem complete_exact (state : N) (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (available : Available state.machine.heap value)
    (normalized : InternedFreshOrdinaryConstraintHeap.Heap
      (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities) state.machine.heap)
    (ranges : Ranges emptyGuard conjoin order value state) :
    ∃ result after, Execution emptyGuard conjoin formulas solver order value state result after ∧
      SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧ Reference formulas solver order value state result ∧
      ∀ api, result = .ok api → ∀ ambient,
        SourceSizedApiLaws.Exact api (fun term => InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) := by
  obtain ⟨result, after, actual, retained, reference⟩ := complete emptyGuard conjoin formulas solver order value state ready available normalized ranges
  exact ⟨result, after, actual, retained, reference,
    fun api success ambient => Reference.exact_queries emptyGuard conjoin formulas solver order value state ready available result api reference success ambient⟩

/-- Actual closed source construction derives every public-entry premise except reached cache capacity. -/
theorem constructed_complete (expression : InternedNestedConstruction.Syntax (Label Formula) (Constraint Formula))
    (source : InternedConstructorTemplates.State (Label Formula) (Constraint Formula))
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value source)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities) expression)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (domainsValid : Cache.Valid domains)
    (ranges : Ranges emptyGuard conjoin order value (initial (bits + 2) ⟨source, domains⟩)) :
    ∃ result after, Execution emptyGuard conjoin formulas solver order value (initial (bits + 2) ⟨source, domains⟩) result after ∧
      SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧
      Reference formulas solver order value (initial (bits + 2) ⟨source, domains⟩) result ∧
      ∀ api, result = .ok api → ∀ ambient,
        SourceSizedApiLaws.Exact api (fun term => InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) := by
  obtain ⟨ready, available, _⟩ := SourceFreshOrdinaryColdNativeTable.constructed expression value source built domains domainsValid
    (bits + 2) emptyGuard conjoin
  have normalized : InternedFreshOrdinaryConstraintHeap.Heap
      (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities) source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryConstraintHeap.build_heap _ expression [] empty (InternedFreshOrdinaryConstraintHeap.empty_heap _) annotations
  exact complete_exact emptyGuard conjoin formulas solver order value _ ready available normalized ranges

end MicroCFTA.SourceFreshOrdinaryNativeEntry
