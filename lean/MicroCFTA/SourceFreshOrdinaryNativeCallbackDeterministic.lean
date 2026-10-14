import MicroCFTA.SourceFreshOrdinaryNativeCallback

/-!
# Unique complete native callback results

Successful native and exposure bounds are stable. Complete cold traces
also have common larger collection bounds. Every complete callback therefore
returns the same Boolean and native cache. Derived completion then gives
correctness and retained invariants for any actual completed execution.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeCallback
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView (Original)

/-- Every complete callback returns the identical Boolean and native cache, regardless of successful bounds. -/
theorem Execution.unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {left right : Value Symbol Guard}
    {state firstAfter secondAfter : SourceRecursiveIntersectionThunks.State width Symbol Guard} {firstResult secondResult : Bool}
    (first : Execution emptyGuard conjoin left right state firstResult firstAfter)
    (second : Execution emptyGuard conjoin left right state secondResult secondAfter) :
    firstResult = secondResult ∧ firstAfter = secondAfter := by
  cases first with
  | done fuel readFuel outer inner minimumFuel state middle value edges exposed final rows native read collected minimum =>
    cases second with
    | done nextFuel nextReadFuel nextOuter nextInner nextMinimumFuel _ nextMiddle nextValue nextEdges nextExposed nextFinal nextRows nextNative nextRead nextCollected nextMinimum =>
      have firstNative := SourceRecursiveIntersectionNative.done_stable emptyGuard conjoin fuel nextFuel _ state middle value native
      have secondNative := SourceRecursiveIntersectionNative.done_stable emptyGuard conjoin nextFuel fuel _ state nextMiddle nextValue nextNative
      rw [Nat.add_comm nextFuel fuel] at secondNative
      have nativeSame := firstNative.symm.trans secondNative
      obtain ⟨rfl, rfl⟩ := SourceRecursiveIntersectionNative.Outcome.done.inj nativeSame
      have firstRead := MergedFreshOrdinaryColdReplay.nodeEdges_stable readFuel nextReadFuel value middle.machine.heap
        (by simp only [read, MergedSourceExposure.Finished])
      have secondRead := MergedFreshOrdinaryColdReplay.nodeEdges_stable nextReadFuel readFuel value middle.machine.heap
        (by simp only [nextRead, MergedSourceExposure.Finished])
      rw [Nat.add_comm nextReadFuel readFuel] at secondRead
      have readSame : MergedSourceExposure.Result.done edges exposed = .done nextEdges nextExposed := by
        rw [← read, ← nextRead]
        exact firstRead.symm.trans secondRead
      obtain ⟨rfl, rfl⟩ := MergedSourceExposure.Result.done.inj readSame
      obtain ⟨firstOuter, firstInner, firstStable⟩ :=
        (SourceFreshOrdinaryColdSharedRows.collect_trace outer inner exposed (fun _ => none) rows [value] final collected).finite
      obtain ⟨secondOuter, secondInner, secondStable⟩ :=
        (SourceFreshOrdinaryColdSharedRows.collect_trace nextOuter nextInner exposed (fun _ => none) nextRows [value] nextFinal nextCollected).finite
      have firstRows := firstStable (max firstOuter secondOuter) (max firstInner secondInner) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      have secondRows := secondStable (max firstOuter secondOuter) (max firstInner secondInner) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      obtain ⟨rfl, rfl⟩ := SourceColdSharedRows.Result.done.inj (firstRows.symm.trans secondRows)
      exact ⟨rfl, rfl⟩

/-- Every actual completed checked callback has the derived exact Boolean, cache growth, and next-call invariants. -/
theorem Execution.correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : Ready emptyGuard conjoin state)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state)
    (result : Bool) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (execution : Execution emptyGuard conjoin left right state result after) :
    Ready emptyGuard conjoin after ∧ Extension state.machine after.machine ∧
      ∀ ambient, result = true ↔ ∃ term,
        InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
        InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term := by
  obtain ⟨expected, final, actual, retained, growth, exactLanguage⟩ :=
    complete emptyGuard conjoin state ready left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  obtain ⟨rfl, rfl⟩ := execution.unique actual
  exact ⟨retained, growth, exactLanguage⟩

end MicroCFTA.SourceFreshOrdinaryNativeCallback
