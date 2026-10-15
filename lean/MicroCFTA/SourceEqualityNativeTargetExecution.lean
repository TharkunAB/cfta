import MicroCFTA.SourceEqualityNativeTargetFold

/-!
# Executable first-seeded native target folds

A common proof bound instruments each native request. Completed folds have
stable values and full native states. A noncompleted request returns its
actual observation; this worker does not resume the enclosing fold.
-/
namespace MicroCFTA.SourceEqualityNativeTargetExecution
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityNativeTargetFold
open InternedGuardedLanguage (meaning)

/-- Execute the tail first, then intersect the next operand in its returned warm state. -/
def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (fuel : Nat) (seed : Value Symbol Guard) :
    List (Value Symbol Guard) → SourceRecursiveIntersectionThunks.State width Symbol Guard →
      SourceRecursiveIntersectionNative.Outcome width Symbol Guard (Value Symbol Guard)
  | [], state => .done seed state
  | value :: values, state => match fold emptyGuard conjoin fuel seed values state with
    | .done tail middle => SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
        (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) middle
    | other => other

/-- Execute the actual empty-list or first-seeded source target branch. -/
def intersectList [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (fuel : Nat) (values : List (Value Symbol Guard))
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    SourceRecursiveIntersectionNative.Outcome width Symbol Guard (Value Symbol Guard) :=
  match values with
  | [] => .done .empty state
  | seed :: rest => fold emptyGuard conjoin fuel seed rest state

/-- Every checked successful folded execution supplies its exact physical request graph. -/
theorem fold_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (seed : Value Symbol Guard)
    (values : List (Value Symbol Guard)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : FoldRanges emptyGuard conjoin seed values before) (result : Value Symbol Guard)
    (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (done : fold emptyGuard conjoin fuel seed values before = .done result after) :
    Fold emptyGuard conjoin seed values before result after := by
  induction ranges generalizing result after with
  | nil =>
      have parts := SourceRecursiveIntersectionNative.Outcome.done.inj done
      cases parts.1; cases parts.2
      exact .nil
  | @cons values before value rest ranges ih =>
      cases tail : fold emptyGuard conjoin fuel seed values before with
      | done output middle =>
          have tailTrace := ih output middle tail
          have step : Step emptyGuard conjoin value output middle result after :=
            .done fuel (ranges output middle tailTrace) (by simpa only [fold, tail] using done)
          exact .cons tailTrace step
      | yielded | failed | blocked => simp only [fold, tail] at done; cases done

/-- Every checked successful target list supplies its exact first-seeded graph. -/
theorem list_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (values : List (Value Symbol Guard))
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ranges : ListRanges emptyGuard conjoin values before)
    (result : Value Symbol Guard) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (done : intersectList emptyGuard conjoin fuel values before = .done result after) :
    IntersectList emptyGuard conjoin values before result after := by
  cases values with
  | nil =>
      have parts := SourceRecursiveIntersectionNative.Outcome.done.inj done
      cases parts.1; cases parts.2
      exact .nil
  | cons seed rest => exact .cons (fold_graph emptyGuard conjoin fuel seed rest before ranges result after done)

/-- A completed right-fold graph supplies one sufficient bound for every native request. -/
theorem fold_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {seed result : Value Symbol Guard}
    {values : List (Value Symbol Guard)} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin seed values before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → fold emptyGuard conjoin fuel seed values before = .done result after := by
  induction trace with
  | nil => exact ⟨0, by intros; rfl⟩
  | cons rest step ih =>
      obtain ⟨restBound, restStable⟩ := ih
      obtain ⟨stepBound, stepStable⟩ := step.stable
      refine ⟨max restBound stepBound, ?_⟩
      intro fuel enough
      simp only [fold, restStable fuel (Nat.le_trans (Nat.le_max_left _ _) enough),
        stepStable fuel (Nat.le_trans (Nat.le_max_right _ _) enough)]

/-- Complete source target-list graphs execute with identical results and full warm states at all larger bounds. -/
theorem list_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {result : Value Symbol Guard}
    {values : List (Value Symbol Guard)} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : IntersectList emptyGuard conjoin values before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → intersectList emptyGuard conjoin fuel values before = .done result after := by
  cases trace with
  | nil => exact ⟨0, by intros; rfl⟩
  | cons trace => exact fold_stable trace

/-- Completed target lists have a unique value and complete native state. -/
theorem list_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {first second : Value Symbol Guard}
    {values : List (Value Symbol Guard)} {before afterFirst afterSecond : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (left : IntersectList emptyGuard conjoin values before first afterFirst)
    (right : IntersectList emptyGuard conjoin values before second afterSecond) : first = second ∧ afterFirst = afterSecond := by
  obtain ⟨firstBound, firstStable⟩ := list_stable left
  obtain ⟨secondBound, secondStable⟩ := list_stable right
  exact SourceRecursiveIntersectionNative.Outcome.done.inj
    ((firstStable (max firstBound secondBound) (Nat.le_max_left _ _)).symm.trans
      (secondStable (max firstBound secondBound) (Nat.le_max_right _ _)))

/-- Checked bounded execution and complete source target-list graphs agree in both directions. -/
theorem execution_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ranges : ListRanges emptyGuard conjoin values before)
    (result : Value Symbol Guard) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    IntersectList emptyGuard conjoin values before result after ↔
      ∃ fuel, intersectList emptyGuard conjoin fuel values before = .done result after := by
  constructor
  · intro trace
    obtain ⟨bound, stable⟩ := list_stable trace
    exact ⟨bound, stable bound (Nat.le_refl _)⟩
  · rintro ⟨fuel, done⟩
    exact list_graph emptyGuard conjoin fuel values before ranges result after done

/-- Captured operands in an earlier real cache remain available for a complete actual target fold. -/
theorem scoped_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base values) (closed : ClosedValues values)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before) (ranges : ListRanges emptyGuard conjoin values before)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ result after, IntersectList emptyGuard conjoin values before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      (∃ bound, ∀ fuel, bound ≤ fuel → intersectList emptyGuard conjoin fuel values before = .done result after) ∧
      ∀ ambient term, meaning holds ambient result term ↔ ListMeaning holds ambient values term := by
  have available : Values before.machine.heap values := fun value member => retained.available value (known value member)
  obtain ⟨result, after, trace, finalReady, keeps, resultAvailable, resultClosed⟩ :=
    SourceEqualityNativeTargetFold.complete emptyGuard conjoin values before ranges ready available closed holds conjoined
  exact ⟨result, after, trace, finalReady, retained.trans keeps, resultAvailable, resultClosed,
    list_stable trace, (trace.verified ready available closed holds conjoined).2.2.2.2⟩

end MicroCFTA.SourceEqualityNativeTargetExecution
