import MicroCFTA.SourceFreshOrdinaryNativeCallback
import MicroCFTA.SourceRecursiveIntersectionNativeCapacityWords

/-!
# Complete native callbacks under actual cache capacity

Reached source cache counters derive every native request-word check.
The existing complete callback then retains its exact Boolean and cache.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeCallback
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView (Original)

/-- Actual cache-capacity checks give finite complete overlap callbacks without a supplied word-safety premise. -/
theorem complete_capacity [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard) (ready : Ready emptyGuard conjoin state)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceRecursiveIntersectionNativeCapacity.CacheRanges bits emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state) :
    ∃ result after, Execution emptyGuard conjoin left right state result after ∧
      Ready emptyGuard conjoin after ∧ Extension state.machine after.machine ∧
      ∀ ambient, result = true ↔ ∃ term,
        InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
        InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term := by
  have words := SourceRecursiveIntersectionNativeCapacity.node_wordRanges bits emptyGuard conjoin
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state ready.valid
    ⟨empty_domain state.machine, leftAvailable, rightAvailable⟩ ranges
  exact complete emptyGuard conjoin state ready left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed words

end MicroCFTA.SourceFreshOrdinaryNativeCallback
