import MicroCFTA.SourceEqualityRequiredSemanticCache
import MicroCFTA.SourceRecursiveIntersectionNativeProduct
import MicroCFTA.SourceRecursiveIntersectionNativeWarmColdExact

/-!
# Actual native intersection effects for equality edit leaves

Successful requests retain their complete native memo state and immediate
constructor cache. Closed available inputs derive original syntax. Actual
native evaluation derives all edit-worker cache fields and the exact product
language. No cold-table traversal is added to the callback.
-/
namespace MicroCFTA.SourceEqualityNativeLeaf
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache

/-- A completed checked native leaf derives all actual edit effects and its exact narrowing language. -/
theorem done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (semantic : SemanticReady state.machine.heap) (target input result : Value Symbol Guard)
    (targetAvailable : Available state.machine.heap target) (inputAvailable : Available state.machine.heap input)
    (targetClosed : target.free = []) (inputClosed : input.free = [])
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) state)
    (actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) state = .done result after)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    Keeps state.machine.heap after.machine.heap ∧ SemanticReady after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, InternedGuardedLanguage.meaning holds ambient result term ↔
        InternedGuardedLanguage.meaning holds ambient input term ∧ InternedGuardedLanguage.meaning holds ambient target term := by
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ :=
    ⟨empty_domain state.machine, targetAvailable, inputAvailable⟩
  have evaluated := SourceRecursiveIntersectionNative.evaluation_of_done emptyGuard conjoin fuel _ state after result actual
  have bounds := evaluated.bounds_of_ranges ranges
  have safe := safe_requestNode IntersectionEmptyDomain.emptyDomain target input state.machine ready
  have certificate := semantic_requestNode IntersectionEmptyDomain.emptyDomain target input state.machine ready
  have correct := bounds.correct (fun current value => Available current.heap value) (by intro value; trivial) safe valid
  have guarded := bounds.guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) safe valid certificate semantic.ready.semantic (by intro value; trivial) semantic.guarded
  have depth := bounds.open_depth_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) safe valid certificate semantic.ready.semantic (by intro value; trivial) semantic.ready.depth
  have budget := bounds.budget_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) safe valid certificate semantic.ready.semantic (by intro value; trivial) semantic.budget
  obtain ⟨steps, _, trace⟩ := SourceRecursiveIntersectionNative.done_trace emptyGuard conjoin fuel _ state after result actual
  have covered := (trace.covered emptyGuard conjoin steps _ _ state after
    semantic.ready.semantic.1.normal.facts.coherent.valid semantic.ready.covered).2
  have finalReady : SourceEqualityRequiredCache.Ready after.machine.heap := ⟨guarded.1, covered, depth.2⟩
  have targetOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original target state.machine.heap
    semantic.ready.semantic.1.normal.facts.coherent targetAvailable targetClosed
  have inputOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original input state.machine.heap
    semantic.ready.semantic.1.normal.facts.coherent inputAvailable inputClosed
  refine ⟨⟨finalReady, correct.growth.heap, correct.growth.history⟩, ⟨finalReady, guarded.2, budget.2⟩,
    correct.result, SourceRecursiveIntersectionNative.done_closed_of_ranges emptyGuard conjoin fuel target input result
      state after valid targetAvailable inputAvailable semantic.ready.semantic ranges actual, ?_⟩
  intro ambient term
  exact (SourceRecursiveIntersectionNative.native_product emptyGuard conjoin fuel target input state after result valid
    targetOriginal inputOriginal targetAvailable inputAvailable targetClosed inputClosed semantic.ready.semantic semantic.guarded
    actual ranges holds conjoined ambient term).trans and_comm

/-- Actual first native requests complete with the exact immediate edit cache and stable returned memo state. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before : InternedConstructorTemplates.State Symbol Guard) (semantic : SemanticReady before)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (target input : Value Symbol Guard)
    (targetAvailable : Available before target) (inputAvailable : Available before input)
    (targetClosed : target.free = []) (inputClosed : input.free = [])
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) (initial width ⟨before, domains⟩))
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ fuel result after,
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure)
        (initial width ⟨before, domains⟩) = .done result after ∧
      Keeps before after.machine.heap ∧ SemanticReady after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      (∀ extra, SourceRecursiveIntersectionNative.execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure)
        (initial width ⟨before, domains⟩) = .done result after) ∧
      ∀ ambient term, InternedGuardedLanguage.meaning holds ambient result term ↔
        InternedGuardedLanguage.meaning holds ambient input term ∧ InternedGuardedLanguage.meaning holds ambient target term := by
  have facts := semantic.ready.semantic.1.normal.facts
  have targetOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original target before facts.coherent targetAvailable targetClosed
  have inputOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original input before facts.coherent inputAvailable inputClosed
  obtain ⟨fuel, result, after, actual, _, _, _, stable⟩ :=
    SourceRecursiveIntersectionNative.cold_node_complete before semantic.ready.semantic semantic.ready.covered domains domainsValid
      holds emptyGuard conjoin target input targetOriginal inputOriginal targetAvailable inputAvailable targetClosed inputClosed ranges
  have checked := done emptyGuard conjoin fuel (initial width ⟨before, domains⟩) after
    (initial_valid width emptyGuard conjoin (⟨before, domains⟩ : Machine Symbol Guard) ⟨facts, domainsValid⟩) semantic target input result targetAvailable inputAvailable
    targetClosed inputClosed ranges actual holds conjoined
  exact ⟨fuel, result, after, actual, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, stable, checked.2.2.2.2⟩

/-- Captured target availability follows from actual cache histories before a later native leaf call. -/
theorem captured_target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (base : InternedConstructorTemplates.State Symbol Guard) (target : Value Symbol Guard) (known : Available base target)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (retained : Keeps base state.machine.heap)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (semantic : SemanticReady state.machine.heap) (input result : Value Symbol Guard) (inputAvailable : Available state.machine.heap input)
    (targetClosed : target.free = []) (inputClosed : input.free = [])
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) state)
    (actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) state = .done result after)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    Keeps base after.machine.heap ∧ SemanticReady after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, InternedGuardedLanguage.meaning holds ambient result term ↔
        InternedGuardedLanguage.meaning holds ambient input term ∧ InternedGuardedLanguage.meaning holds ambient target term := by
  have checked := done emptyGuard conjoin fuel state after valid semantic target input result (retained.available target known)
    inputAvailable targetClosed inputClosed ranges actual holds conjoined
  exact ⟨retained.trans checked.1, checked.2⟩

end MicroCFTA.SourceEqualityNativeLeaf
