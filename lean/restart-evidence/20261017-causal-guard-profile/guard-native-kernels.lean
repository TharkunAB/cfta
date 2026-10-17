import MicroCFTA.SourceCurrentConstrainedCapGuardNative

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.NativeGuardKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
variable {Symbol Guard : Type}

/-- Closed construction supplies every cache invariant for a later actual optional binder. -/
theorem constructed_optional [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (expression : Syntax Symbol Guard) (pair : Nat × Nat) :
    ∃ (body value : Value Symbol Guard) (middle after : State Symbol Guard),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done body middle ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body middle = .done value after ∧
      SourceCurrentConstrainedCapGuardHeap.Heap valid middle ∧
      SourceCurrentConstrainedCapGuardHeap.Heap valid after ∧
      SourceCurrentHereditaryConstruction.MuStored valid after ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap after ∧
      InternedRecordCoherence.Covered [] after ∧ Available after value := by
  obtain ⟨body, middle, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have ready := SourceEqualityRequiredCache.constructed expression body middle built
  have available := (InternedFreshOrdinaryFacts.build_verified expression [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)).result body middle built
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap valid middle := by
    simpa only [built, Outcome.state] using SourceCurrentConstrainedCapGuardExecution.closed_heap valid expression
  obtain ⟨value, after, done, semantic, retained, covered, output, _growth, _history⟩ :=
    SourceCurrentConstrainedCapGuardNative.complete valid pair body middle ready.semantic available ready.covered guards
  exact ⟨body, value, middle, after, built, done, guards, retained,
    SourceCurrentConstrainedCapGuardNative.stored valid after retained, semantic, covered, output⟩

#print axioms constructed_optional
#check @constructed_optional
end MicroCFTA.NativeGuardKernels
