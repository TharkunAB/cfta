import MicroCFTA.SourceCurrentAllocatedNativeWarmQuery

open MicroCFTA
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

#check SourceCurrentAllocatedNativeWarmQuery.Receipt.done
#check SourceCurrentAllocatedNativeWarmQuery.input_meaning
#check SourceCurrentAllocatedNativeWarmQuery.query_complete
#print axioms SourceCurrentAllocatedNativeWarmQuery.Receipt.done
#print axioms SourceCurrentAllocatedNativeWarmQuery.input_meaning
#print axioms SourceCurrentAllocatedNativeWarmQuery.query_complete

namespace MicroCFTA.WarmQueryKernelProbe
variable {width : Nat}

theorem actual_complete_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver))
      (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (scopeCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
    (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (growth : Grows source state.native.machine.heap)
    (history : Cache.Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftValid : inputs.valid (inputOf left)) (rightValid : inputs.valid (inputOf right))
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value after,
      execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after ∧
      (∀ extra, execute (fuel + extra + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after) ∧
      Good after ∧ SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] ∧
      ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeWarmQuery.query_complete
    source facts formulas solver inputs state valid contextual scopeCache semantic idle growth history
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid ranges
  refine ⟨fuel, value, after, receipt.done, ?_, receipt.good, receipt.scopedCache, receipt.idle, receipt.closed, receipt.meaning⟩
  intro extra
  simpa only [Nat.add_assoc, Nat.add_comm 1 extra] using
    done_stable (fuel + 1) extra _ state after value receipt.done

example (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (value : Value Symbol Guard) (original : Original value) (available : Available source value)
    (closed : value.free = []) (valid : inputs.valid (inputOf value))
    (first second : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds first value term ↔ InternedGuardedLanguage.meaning holds second value term :=
  (SourceCurrentAllocatedNativeWarmQuery.input_meaning source facts holds inputs value original available closed valid first term).trans
    (SourceCurrentAllocatedNativeWarmQuery.input_meaning source facts holds inputs value original available closed valid second term).symm

end MicroCFTA.WarmQueryKernelProbe
#print axioms MicroCFTA.WarmQueryKernelProbe.actual_complete_stable
