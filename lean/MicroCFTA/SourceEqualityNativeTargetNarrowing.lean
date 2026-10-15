import MicroCFTA.SourceEqualityNativeTargetExecution

/-!
# Concrete target-list construction followed by native narrowing

The input remains available while its target list is intersected. The next
native request uses that actual target and the returned warm native state.
This graph describes one target construction and one application.
-/
namespace MicroCFTA.SourceEqualityNativeTargetNarrowing
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityNativeTargetFold
open InternedGuardedLanguage (meaning)

/-- One actual target-list construction followed by its actual native leaf request. -/
inductive Narrow [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (input : Value Symbol Guard) : SourceRecursiveIntersectionThunks.State width Symbol Guard →
      Value Symbol Guard → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | apply (target : IntersectList emptyGuard conjoin values before value middle)
      (leaf : Step emptyGuard conjoin value input middle result after) : Narrow emptyGuard conjoin values input before result after

/-- Exact target conjunction and immediate narrowing compose in the same full native state. -/
theorem Narrow.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {values : List (Value Symbol Guard)} {input result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Narrow emptyGuard conjoin values input before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (inputAvailable : Available before.machine.heap input) (inputClosed : input.free = [])
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, meaning holds ambient result term ↔ meaning holds ambient input term ∧ ListMeaning holds ambient values term := by
  cases trace with
  | apply target leaf =>
      have targetFacts := target.verified ready available closed holds conjoined
      have leafFacts := leaf.verified targetFacts.1 targetFacts.2.2.1
        (targetFacts.2.1.available _ inputAvailable) targetFacts.2.2.2.1 inputClosed holds conjoined
      refine ⟨leafFacts.1, targetFacts.2.1.trans leafFacts.2.1, leafFacts.2.2.1, leafFacts.2.2.2.1, ?_⟩
      intro ambient term
      exact (leafFacts.2.2.2.2 ambient term).trans (and_congr Iff.rfl (targetFacts.2.2.2.2 ambient term))

/-- Only actual completed target-list states enter the final native word check. -/
structure Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (input : Value Symbol Guard) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop where
  targets : ListRanges emptyGuard conjoin values before
  leaf : ∀ target middle, IntersectList emptyGuard conjoin values before target middle →
    SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) middle

/-- Local warm progress derives complete target construction and leaf application from scoped word checks. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard)) (input : Value Symbol Guard)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin before)
    (ranges : Ranges emptyGuard conjoin values input before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (inputAvailable : Available before.machine.heap input) (inputClosed : input.free = [])
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ result after, Narrow emptyGuard conjoin values input before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, meaning holds ambient result term ↔ meaning holds ambient input term ∧ ListMeaning holds ambient values term := by
  obtain ⟨target, middle, targets, targetReady, keeps, targetAvailable, targetClosed⟩ :=
    SourceEqualityNativeTargetFold.complete emptyGuard conjoin values before ranges.targets ready available closed holds conjoined
  obtain ⟨result, after, leaf, _⟩ := SourceEqualityNativeScoped.complete emptyGuard conjoin middle targetReady target input
    targetAvailable (keeps.available input inputAvailable) targetClosed inputClosed (ranges.leaf target middle targets) holds conjoined
  have trace : Narrow emptyGuard conjoin values input before result after := .apply targets leaf
  exact ⟨result, after, trace, trace.verified ready available closed inputAvailable inputClosed holds conjoined⟩

/-- Operands and input captured in a real earlier heap retain their scope through both actual stages. -/
theorem scoped_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard)) (input : Value Symbol Guard)
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base values) (inputKnown : Available base input)
    (closed : ClosedValues values) (inputClosed : input.free = [])
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before) (ranges : Ranges emptyGuard conjoin values input before)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ result after, Narrow emptyGuard conjoin values input before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, meaning holds ambient result term ↔ meaning holds ambient input term ∧ ListMeaning holds ambient values term := by
  obtain ⟨result, after, trace, finalReady, keeps, rest⟩ := complete emptyGuard conjoin values input before ready ranges
    (fun value member => retained.available value (known value member)) closed (retained.available input inputKnown) inputClosed holds conjoined
  exact ⟨result, after, trace, finalReady, retained.trans keeps, rest⟩

end MicroCFTA.SourceEqualityNativeTargetNarrowing
