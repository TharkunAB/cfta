import MicroCFTA.SourceRecursiveIntersectionNativeConstructorSite

/-!
# Derived complete coverage at actual native constructor sites

Actual yielded prefixes preserve all incoming payloads. A constructor block
therefore derives complete coverage before its original optional-binder
call when the initial cache is complete. Completed repaired construction
from empty caches supplies that initial coverage for arbitrary nested syntax.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedNestedConstruction (Syntax)

/-- A bounded pending native result derives its exact source site and the site's original payload coverage. -/
theorem constructor_trace_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (code remaining : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : NodeKey)
    (valid : InternedConstructorTemplates.Valid state.machine.heap) (covered : Covered pending state.machine.heap)
    (blocked : execute emptyGuard conjoin fuel code state = .blocked (.constructor key) remaining after) :
    ∃ steps before pair body next heap, steps < fuel ∧
      Steps emptyGuard conjoin steps code state (.optionalBinder pair body next) before ∧
      remaining = .optionalBinder pair body next ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.machine.heap = .pending key heap ∧
      after = advance before {before.machine with heap := heap} ∧
      InternedConstructorTemplates.Valid before.machine.heap ∧ Covered pending before.machine.heap := by
  obtain ⟨steps, before, pair, body, next, heap, smaller, trace, original, constructed, final⟩ :=
    constructor_trace emptyGuard conjoin fuel code remaining state after key blocked
  have coverage := trace.covered emptyGuard conjoin steps code _ state before valid covered
  exact ⟨steps, before, pair, body, next, heap, smaller, trace, original, constructed, final, coverage⟩

/-- A completed repaired source build supplies payload coverage through every later native yielded prefix. -/
theorem constructed_prefix_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (value : Value Symbol Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value source)
    (domains : Cache.State DomainKey) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code next : Code Symbol Guard A) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin fuel code (initial width ⟨source, domains⟩) next after) :
    InternedConstructorTemplates.Valid after.machine.heap ∧ Covered [] after.machine.heap := by
  have valid : InternedConstructorTemplates.Valid source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      (InternedFreshOrdinaryGrowth.build_correct expression [] empty empty_valid).1
  exact trace.covered emptyGuard conjoin fuel code next (initial width ⟨source, domains⟩) after valid
    (InternedFreshOrdinaryCoverage.closed_covered expression value source built)

/-- An actual native constructor block after source construction derives complete coverage before the call. -/
theorem constructed_constructor_site [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (value : Value Symbol Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value source)
    (domains : Cache.State DomainKey) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code remaining : Code Symbol Guard A) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : NodeKey)
    (blocked : execute emptyGuard conjoin fuel code (initial width ⟨source, domains⟩) = .blocked (.constructor key) remaining after) :
    ∃ steps before pair body next heap, steps < fuel ∧
      Steps emptyGuard conjoin steps code (initial width ⟨source, domains⟩) (.optionalBinder pair body next) before ∧
      remaining = .optionalBinder pair body next ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.machine.heap = .pending key heap ∧
      after = advance before {before.machine with heap := heap} ∧
      InternedConstructorTemplates.Valid before.machine.heap ∧ Covered [] before.machine.heap := by
  have valid : InternedConstructorTemplates.Valid source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      (InternedFreshOrdinaryGrowth.build_correct expression [] empty empty_valid).1
  exact constructor_trace_covered emptyGuard conjoin fuel code remaining (initial width ⟨source, domains⟩) after key valid
    (InternedFreshOrdinaryCoverage.closed_covered expression value source built) blocked

end MicroCFTA.SourceRecursiveIntersectionNative
