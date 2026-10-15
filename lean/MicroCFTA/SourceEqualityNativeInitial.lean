import MicroCFTA.SourceEqualityNativeScoped

/-!
# Initial native equality scope from an actual semantic constructor heap

Initialization creates empty domain and native memo tables. Constructor
readiness derives native validity and idle scope. No target construction,
completed native request, or native semantic law is supplied.
-/
namespace MicroCFTA.SourceEqualityNativeInitial
open InternedConstructorTemplates SourceEqualityNativeScoped SourceEqualityRequiredSemanticCache

/-- Start native equality work at the actual constructor heap with empty domain and memo tables. -/
def cold (width : Nat) (heap : State Symbol Guard) : SourceRecursiveIntersectionThunks.State width Symbol Guard :=
  SourceRecursiveIntersectionThunks.initial width ⟨heap, Cache.emptyState⟩

/-- Actual semantic constructor readiness supplies every initial native scope invariant. -/
theorem ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (heap : State Symbol Guard) (semantic : SemanticReady heap) :
    IdleReady emptyGuard conjoin (cold width heap) :=
  ⟨SourceRecursiveIntersectionThunks.initial_valid width emptyGuard conjoin _ ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩,
    SourceRecursiveIntersectionNative.idle_initial _, semantic⟩

end MicroCFTA.SourceEqualityNativeInitial
