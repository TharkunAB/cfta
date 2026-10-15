import MicroCFTA.SourceEqualityDemandTargetWorker

/-!
# Successful demanded target execution gives actual request graphs

Each successful stage retains the literal projection, merge, or native
receipt. Native range checks use only the actual completed demand prefixes.
No whole-worker graph or language law is supplied.
-/
namespace MicroCFTA.SourceEqualityDemandTargetWorkerSound
open InternedConstructorTemplates SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityDemandTarget
open SourceEqualityDemandTargetComplete SourceEqualityDemandTargetWorker

/-- Successful sequencing identifies its exact completed prefix and continuation. -/
theorem bind_done (first : Result width Symbol Guard A) (next : A → NativeState width Symbol Guard → Result width Symbol Guard B)
    (result : B) (after : NativeState width Symbol Guard) : first.bind next = .done result after ↔
      ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro actual; exact ⟨value, state, rfl, actual⟩
      · rintro ⟨value, state, same, actual⟩; cases same; exact actual
  | projection | merge | native => simp [Result.bind]

/-- Successful projection wrappers retain the actual forest read and its advanced full native state. -/
theorem projection_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : projection fuel readFuel path values before = .done result after) :
    ∃ heap, SourceEqualityProjectionGraph.Forest path values before.machine.heap result heap ∧ after = advanceHeap before heap := by
  cases actual : SourceEqualityProjectionWorker.forest fuel readFuel path values before.machine.heap with
  | pending | unresolved | exhausted => simp only [projection, actual] at done; cases done
  | done value heap =>
      have parts := Result.done.inj (by simpa only [projection, actual] using done)
      cases parts.1
      exact ⟨heap, SourceEqualityProjectionWorkerSound.forest_graph fuel readFuel path values before.machine.heap result heap actual, parts.2.symm⟩

/-- Successful merge wrappers retain their literal bounded general source receipt. -/
theorem merge_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) (fuel : Nat)
    (value : Value Symbol Guard) (before : NativeState width Symbol Guard) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : merge clear top fuel value before = .done result after) : SourceEqualityNativeMerge.Merge clear top value before result after := by
  cases actual : SourceMergedWorker.execute clear top fuel value before.machine.heap with
  | failed => simp only [merge, actual] at done; cases done
  | done value heap =>
      have parts := Result.done.inj (by simpa only [merge, actual] using done)
      cases parts.1; cases parts.2
      exact .done fuel actual

/-- Successful executable operand demand agrees with its actual projection-and-merge graph. -/
theorem operand_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard)
    (fuel readFuel comparisonFuel : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : operand clear top fuel readFuel comparisonFuel path values before = .done result after) : Operand clear top path values before result after := by
  obtain ⟨projected, middle, projectedDone, mergedDone⟩ := (bind_done _ _ result after).mp done
  obtain ⟨heap, projectedTrace, rfl⟩ := projection_graph fuel readFuel path values before projected middle projectedDone
  exact .force projectedTrace (merge_graph clear top comparisonFuel projected _ result after mergedDone)

/-- Successful checked native wrappers retain the actual request and its actual final state. -/
theorem leaf_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (value tail : Value Symbol Guard) (before : NativeState width Symbol Guard) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) before)
    (done : leaf emptyGuard conjoin fuel value tail before = .done result after) : Step emptyGuard conjoin value tail before result after := by
  cases actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) before with
  | yielded | failed | blocked => simp only [leaf, actual] at done; cases done
  | done output final =>
      have parts := Result.done.inj (by simpa only [leaf, actual] using done)
      cases parts.1; cases parts.2
      exact .done fuel ranges actual

/-- Every checked successful demanded right fold supplies its literal interleaved request graph. -/
theorem fold_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (fuel readFuel comparisonFuel nativeFuel : Nat) (values : List (Value Symbol Guard))
    (seed : List Int) (paths : List (List Int)) (before : NativeState width Symbol Guard)
    (ranges : FoldRanges emptyGuard conjoin clear top values seed paths before) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : fold emptyGuard conjoin clear top fuel readFuel comparisonFuel nativeFuel values seed paths before = .done result after) :
    Fold emptyGuard conjoin clear top values seed paths before result after := by
  induction paths generalizing before result after with
  | nil => exact .nil (operand_graph clear top fuel readFuel comparisonFuel seed values before result after done)
  | cons path paths ih =>
      cases ranges with
      | cons restPlan stepPlan =>
          obtain ⟨value, middle, operandDone, later⟩ := (bind_done _ _ result after).mp done
          have operandTrace := operand_graph clear top fuel readFuel comparisonFuel path values before value middle operandDone
          obtain ⟨tail, final, restDone, stepDone⟩ := (bind_done _ _ result after).mp later
          have restTrace := ih middle (restPlan value middle operandTrace) tail final restDone
          exact .cons operandTrace restTrace (leaf_graph emptyGuard conjoin nativeFuel value tail final result after
            (stepPlan value middle operandTrace tail final restTrace) stepDone)

/-- Checked successful target execution agrees with the actual empty or first-seeded source graph. -/
theorem target_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (fuel readFuel comparisonFuel nativeFuel : Nat) (values : List (Value Symbol Guard))
    (paths : List (List Int)) (before : NativeState width Symbol Guard) (ranges : TargetRanges emptyGuard conjoin clear top values paths before)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : target emptyGuard conjoin clear top fuel readFuel comparisonFuel nativeFuel values paths before = .done result after) :
    Target emptyGuard conjoin clear top values paths before result after := by
  cases paths with
  | nil => have parts := Result.done.inj done; cases parts.1; cases parts.2; exact .nil
  | cons seed rest => exact .cons (fold_graph emptyGuard conjoin clear top fuel readFuel comparisonFuel nativeFuel values seed rest before ranges result after done)

end MicroCFTA.SourceEqualityDemandTargetWorkerSound
