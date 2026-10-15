import MicroCFTA.SourceEqualityNativeLeaf
import MicroCFTA.SourceRecursiveIntersectionNativeWarmSuccessful

/-!
# Scoped native intersection requests between equality operations

The state retains the actual constructor cache, domain cache, and both native
memo tables. Completed requests return idle tables for the next request.
Constructor-cache growth advances this same state without resetting tables.
-/
namespace MicroCFTA.SourceEqualityNativeScoped
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)

/-- All premises needed between complete native requests, including warm memo tables. -/
structure IdleReady [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop where
  valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state
  idle : SourceRecursiveIntersectionNative.Idle state
  semantic : SemanticReady state.machine.heap

/-- Advance the actual native state after a constructor-only effect. -/
def advanceHeap (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (heap : InternedConstructorTemplates.State Symbol Guard) : SourceRecursiveIntersectionThunks.State width Symbol Guard :=
  advance state {state.machine with heap := heap}

/-- Actual constructor effects retain domain and memo state and every next-call premise. -/
theorem IdleReady.advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {state : SourceRecursiveIntersectionThunks.State width Symbol Guard} (ready : IdleReady emptyGuard conjoin state)
    (heap : InternedConstructorTemplates.State Symbol Guard) (keeps : Keeps state.machine.heap heap)
    (semantic : SemanticReady heap) : IdleReady emptyGuard conjoin (advanceHeap state heap) := by
  refine ⟨advance_valid width emptyGuard conjoin state ready.valid _
    ⟨semantic.ready.semantic.1.normal.facts, ready.valid.machine.2⟩
    ⟨keeps.growth, keeps.history, extends_refl _⟩, ready.idle.advance _ _ , semantic⟩

/-- One actual checked empty-domain native request at its real cache scope. -/
inductive Step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Value Symbol Guard → Value Symbol Guard → SourceRecursiveIntersectionThunks.State width Symbol Guard →
      Value Symbol Guard → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | done (fuel : Nat)
      (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
        (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before)
      (actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
        (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before = .done result after) :
      Step emptyGuard conjoin target input before result after

/-- Any completed scoped request derives idle warm state, immediate cache effects, and exact intersection. -/
theorem Step.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Step emptyGuard conjoin target input before result after) (ready : IdleReady emptyGuard conjoin before)
    (targetAvailable : Available before.machine.heap target) (inputAvailable : Available before.machine.heap input)
    (targetClosed : target.free = []) (inputClosed : input.free = [])
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, meaning holds ambient result term ↔ meaning holds ambient input term ∧ meaning holds ambient target term := by
  cases trace with
  | done fuel ranges actual =>
      have nodeReady : NodeReady before.machine ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ :=
        ⟨empty_domain _, targetAvailable, inputAvailable⟩
      have correct := SourceRecursiveIntersectionNative.done_correct_of_ranges emptyGuard conjoin _ before after result
        (fun current value => Available current.heap value) (by intro value; trivial)
        (safe_requestNode _ _ _ _ nodeReady) ready.valid ranges fuel actual
      have idle := SourceRecursiveIntersectionNative.done_idle emptyGuard conjoin fuel _ before after result
        (by intro value; trivial) (SourceRecursiveIntersectionNative.shape_of_valid emptyGuard conjoin before ready.valid) ready.idle actual
      have checked := SourceEqualityNativeLeaf.done emptyGuard conjoin fuel before after ready.valid ready.semantic
        target input result targetAvailable inputAvailable targetClosed inputClosed ranges actual holds conjoined
      exact ⟨⟨correct.valid, idle, checked.2.1⟩, checked.1, checked.2.2⟩

/-- Every scoped idle warm request completes from its actual word-range checks. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin before)
    (target input : Value Symbol Guard) (targetAvailable : Available before.machine.heap target)
    (inputAvailable : Available before.machine.heap input) (targetClosed : target.free = []) (inputClosed : input.free = [])
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ result after, Step emptyGuard conjoin target input before result after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, meaning holds ambient result term ↔ meaning holds ambient input term ∧ meaning holds ambient target term := by
  have targetOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original target before.machine.heap
    ready.semantic.ready.semantic.1.normal.facts.coherent targetAvailable targetClosed
  have inputOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original input before.machine.heap
    ready.semantic.ready.semantic.1.normal.facts.coherent inputAvailable inputClosed
  obtain ⟨fuel, result, after, actual, _⟩ := SourceRecursiveIntersectionNative.warm_node_complete emptyGuard conjoin before
    ready.valid ready.idle ready.semantic.ready.semantic ready.semantic.ready.covered holds target input
    targetOriginal inputOriginal targetAvailable inputAvailable targetClosed inputClosed ranges
  have trace : Step emptyGuard conjoin target input before result after := .done fuel ranges actual
  exact ⟨result, after, trace, trace.verified ready targetAvailable inputAvailable targetClosed inputClosed holds conjoined⟩

/-- Completed request bounds remain stable with the same full native state. -/
theorem Step.stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Step emptyGuard conjoin target input before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before = .done result after := by
  cases trace with
  | done bound _ actual =>
      refine ⟨bound, ?_⟩
      intro fuel enough
      have stable := SourceRecursiveIntersectionNative.done_stable emptyGuard conjoin bound (fuel - bound) _ before after result actual
      simpa only [show bound + (fuel - bound) = fuel by omega] using stable

end MicroCFTA.SourceEqualityNativeScoped
