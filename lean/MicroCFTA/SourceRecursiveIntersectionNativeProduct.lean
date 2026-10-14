import MicroCFTA.SourceRecursiveIntersectionKernelProduct
import MicroCFTA.SourceRecursiveIntersectionNativeApi
import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate
import MicroCFTA.SourceRecursiveIntersectionNativeGuardedHeap

/-!
# Actual checked native intersection has exact product language

Native completion supplies a completed kernel run. Actual native evaluation
retains the independent-language probe heap. The derived kernel theorem
then gives the complete original-input intersection language.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)

/-- Actual native intersection accepts precisely the common finite terms of its closed original inputs. -/
theorem native_product [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (left right : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state.machine.heap)
    (guarded : InternedGuardedProbeHeap.Heap state.machine.heap)
    (done : execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds ambient value term ↔
      InternedGuardedLanguage.meaning holds ambient left term ∧ InternedGuardedLanguage.meaning holds ambient right term := by
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain state.machine, leftAvailable, rightAvailable⟩
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  have bounds := evaluated.bounds_of_ranges ranges
  obtain ⟨_, _, _, bound, completed⟩ := native_node_correct emptyGuard conjoin fuel _ state after value valid ready done bounds
  have retained := bounds.guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode IntersectionEmptyDomain.emptyDomain left right state.machine ready) valid
    (semantic_requestNode IntersectionEmptyDomain.emptyDomain left right state.machine ready) semantic (by intro value; trivial) guarded
  exact SourceRecursiveIntersectionKernel.execute_product emptyGuard conjoin (bound + 0) state.machine after.machine valid.machine semantic retained.2
    holds conjoined left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed value (completed 0) ambient term

end MicroCFTA.SourceRecursiveIntersectionNative
