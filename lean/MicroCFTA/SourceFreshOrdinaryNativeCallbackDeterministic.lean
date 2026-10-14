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

/-- Successful native bounds retain the identical returned record and memo state. -/
theorem native_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {left right : Value Symbol Guard}
    (firstFuel secondFuel : Nat) {state firstAfter secondAfter : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {firstValue secondValue : Value Symbol Guard}
    (first : SourceRecursiveIntersectionNative.execute emptyGuard conjoin firstFuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done firstValue firstAfter)
    (second : SourceRecursiveIntersectionNative.execute emptyGuard conjoin secondFuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done secondValue secondAfter) :
    firstValue = secondValue ∧ firstAfter = secondAfter := by
  have firstStable := SourceRecursiveIntersectionNative.done_stable emptyGuard conjoin firstFuel secondFuel _ state firstAfter firstValue first
  have secondStable := SourceRecursiveIntersectionNative.done_stable emptyGuard conjoin secondFuel firstFuel _ state secondAfter secondValue second
  rw [Nat.add_comm secondFuel firstFuel] at secondStable
  exact SourceRecursiveIntersectionNative.Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Every complete callback returns the identical Boolean and native cache, including the empty-exposure early return. -/
theorem Execution.unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {left right : Value Symbol Guard}
    {state firstAfter secondAfter : SourceRecursiveIntersectionThunks.State width Symbol Guard} {firstResult secondResult : Bool}
    (first : Execution emptyGuard conjoin left right state firstResult firstAfter)
    (second : Execution emptyGuard conjoin left right state secondResult secondAfter) :
    firstResult = secondResult ∧ firstAfter = secondAfter := by
  cases first with
  | empty fuel readFuel state middle value exposed native read =>
    cases second with
    | empty nextFuel nextReadFuel _ nextMiddle nextValue nextExposed nextNative nextRead =>
      obtain ⟨rfl, rfl⟩ := native_unique fuel nextFuel native nextNative
      obtain ⟨_, rfl⟩ := read_unique readFuel nextReadFuel value middle.machine.heap [] [] exposed nextExposed read nextRead
      exact ⟨rfl, rfl⟩
    | done nextFuel nextReadFuel nextOuter nextInner nextMinimumFuel _ nextMiddle nextValue nextEdges nextExposed nextFinal nextRows nonempty nextNative nextRead nextCollected nextMinimum =>
      obtain ⟨rfl, rfl⟩ := native_unique fuel nextFuel native nextNative
      obtain ⟨rfl, _⟩ := read_unique readFuel nextReadFuel value middle.machine.heap [] nextEdges exposed nextExposed read nextRead
      cases nonempty
  | done fuel readFuel outer inner minimumFuel state middle value edges exposed final rows nonempty native read collected minimum =>
    cases second with
    | empty nextFuel nextReadFuel _ nextMiddle nextValue nextExposed nextNative nextRead =>
      obtain ⟨rfl, rfl⟩ := native_unique fuel nextFuel native nextNative
      obtain ⟨rfl, _⟩ := read_unique readFuel nextReadFuel value middle.machine.heap edges [] exposed nextExposed read nextRead
      cases nonempty
    | done nextFuel nextReadFuel nextOuter nextInner nextMinimumFuel _ nextMiddle nextValue nextEdges nextExposed nextFinal nextRows nextNonempty nextNative nextRead nextCollected nextMinimum =>
      obtain ⟨rfl, rfl⟩ := native_unique fuel nextFuel native nextNative
      obtain ⟨rfl, rfl⟩ := read_unique readFuel nextReadFuel value middle.machine.heap edges nextEdges exposed nextExposed read nextRead
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
