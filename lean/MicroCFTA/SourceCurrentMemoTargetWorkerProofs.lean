import MicroCFTA.SourceCurrentMemoTargetWorker
import MicroCFTA.SourceCurrentMemoDemandTarget
import MicroCFTA.SourceCurrentMemoMergeWorkerProofs
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Actual target graphs and stable five-stage bounds

Successful stages supply their literal projection, recursive memo-aware
merge and checked native receipts. Every finite graph supplies five stable
bounds at its exact intermediate native states and completed tables.
Native word-range plans refer only to actual reached prefixes.
-/
namespace MicroCFTA.SourceCurrentMemoTargetWorkerProofs
open InternedConstructorTemplates SourceEqualityNativeScoped
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoTargetOperand SourceCurrentMemoDemandTarget SourceCurrentMemoTargetWorker

/-- Successful sequencing identifies the actual returned native scope and completed table. -/
theorem bind_done (first : Outcome width Symbol Guard)
    (next : Value Symbol Guard → NativeState width Symbol Guard → Memo Symbol Guard → Outcome width Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard) :
    first.bind next = .done result after saved ↔
      ∃ value middle current, first = .done value middle current ∧ next value middle current = .done result after saved := by
  cases first with
  | done value state memo =>
      constructor
      · intro actual; exact ⟨value, state, memo, rfl, actual⟩
      · rintro ⟨_, _, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, _, impossible, _⟩; cases impossible

/-- Successful projection retains its actual forest graph and unchanged completed table. -/
theorem projection_sound [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard)
    (done : projection fuel readFuel path values before memo = .done result after saved) :
    ∃ heap, SourceEqualityProjectionGraph.Forest path values before.machine.heap result heap ∧
      after = advanceHeap before heap ∧ saved = memo := by
  cases actual : SourceEqualityProjectionWorker.forest fuel readFuel path values before.machine.heap with
  | pending | unresolved | exhausted => simp only [projection, actual] at done; cases done
  | done value heap =>
      simp only [projection, actual] at done
      cases done
      exact ⟨heap, SourceEqualityProjectionWorkerSound.forest_graph _ _ _ _ _ _ _ actual, rfl, rfl⟩

/-- A successful merge wrapper derives the actual recursive memo-aware Call. -/
theorem merge_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (mergeFuel selectionFuel : Nat) (value : Value Symbol Guard)
    (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard) (result : Value Symbol Guard)
    (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard)
    (done : merge clear top mergeFuel selectionFuel value before memo = .done result after saved) :
    SourceCurrentMemoMergeNative.Merge clear top value before memo result after saved := by
  cases actual : SourceCurrentMemoMergeWorker.call clear top mergeFuel selectionFuel value before.machine.heap memo with
  | failed => simp only [merge, actual] at done; cases done
  | done value heap current =>
      simp only [merge, actual] at done
      cases done
      exact .done (SourceCurrentMemoMergeWorkerProofs.call_sound actual)

/-- Successful operand execution derives projection followed by the same actual merge. -/
theorem operand_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (projectionFuel readFuel mergeFuel selectionFuel : Nat)
    (path : List Int) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard)
    (done : operand clear top projectionFuel readFuel mergeFuel selectionFuel path values before memo = .done result after saved) :
    Operand clear top path values before memo result after saved := by
  obtain ⟨projected, middle, current, projectedDone, mergedDone⟩ := (bind_done _ _ result after saved).mp done
  obtain ⟨heap, projectedTrace, rfl, rfl⟩ := projection_sound projectionFuel readFuel path values before memo projected middle current projectedDone
  exact .force projectedTrace (merge_sound clear top mergeFuel selectionFuel projected _ _ result after saved mergedDone)

/-- A checked completed native stage retains its actual Step and the same completed merge table. -/
theorem leaf_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (value tail : Value Symbol Guard)
    (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) before)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard)
    (done : leaf emptyGuard conjoin fuel value tail before memo = .done result after saved) :
    Step emptyGuard conjoin value tail before result after ∧ saved = memo := by
  cases actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) before with
  | yielded | failed | blocked => simp only [leaf, actual] at done; cases done
  | done output final =>
      simp only [leaf, actual] at done
      cases done
      exact ⟨.done fuel ranges actual, rfl⟩

/-- Actual-prefix word plans turn a successful fold into its exact interleaved graph. -/
theorem fold_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat) (values : List (Value Symbol Guard))
    (seed : List Int) (paths : List (List Int)) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (ranges : FoldRanges emptyGuard conjoin clear top values seed paths before memo)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard)
    (done : fold emptyGuard conjoin clear top projectionFuel readFuel mergeFuel selectionFuel nativeFuel
      values seed paths before memo = .done result after saved) :
    Fold emptyGuard conjoin clear top values seed paths before memo result after saved := by
  induction paths generalizing before memo result after saved with
  | nil => exact .nil (operand_sound clear top projectionFuel readFuel mergeFuel selectionFuel seed values before memo result after saved done)
  | cons path paths ih =>
      cases ranges with
      | cons restPlan stepPlan =>
          obtain ⟨value, middle, current, operandDone, later⟩ := (bind_done _ _ result after saved).mp done
          have own := operand_sound clear top projectionFuel readFuel mergeFuel selectionFuel path values before memo value middle current operandDone
          obtain ⟨tail, final, completed, restDone, stepDone⟩ := (bind_done _ _ result after saved).mp later
          have rest := ih middle current (restPlan value middle current own) tail final completed restDone
          obtain ⟨step, rfl⟩ := leaf_sound emptyGuard conjoin nativeFuel value tail final completed
            (stepPlan value middle current own tail final completed rest) result after saved stepDone
          exact .cons own rest step

/-- Checked successful target execution is the actual empty or first-seeded target graph. -/
theorem target_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat) (values : List (Value Symbol Guard))
    (paths : List (List Int)) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
    (ranges : TargetRanges emptyGuard conjoin clear top values paths before memo)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard)
    (done : target emptyGuard conjoin clear top projectionFuel readFuel mergeFuel selectionFuel nativeFuel
      values paths before memo = .done result after saved) :
    Target emptyGuard conjoin clear top values paths before memo result after saved := by
  cases paths with
  | nil => cases done; exact .nil
  | cons seed paths => exact .cons (fold_sound emptyGuard conjoin clear top projectionFuel readFuel mergeFuel selectionFuel nativeFuel
      values seed paths before memo ranges result after saved done)

/-- Every larger five-stage bound returns the same target and its exact two states. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard) : Prop :=
  ∃ projection head merge selection native, ∀ p h m s n,
    projection ≤ p → head ≤ h → merge ≤ m → selection ≤ s → native ≤ n → evaluation p h m s n = .done result after saved

/-- Stable stages combine five bounds at the actual intermediate native scope and merge table. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard)
    (next : Nat → Nat → Nat → Nat → Nat → Value Symbol Guard → NativeState width Symbol Guard → Memo Symbol Guard → Outcome width Symbol Guard)
    (value : Value Symbol Guard) (middle : NativeState width Symbol Guard) (current : Memo Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) (saved : Memo Symbol Guard)
    (one : StableRun first value middle current) (two : StableRun (fun p h m s n => next p h m s n value middle current) result after saved) :
    StableRun (fun p h m s n => (first p h m s n).bind (next p h m s n)) result after saved := by
  obtain ⟨p, h, m, s, n, done⟩ := one
  obtain ⟨laterP, laterH, laterM, laterS, laterN, nextDone⟩ := two
  refine ⟨max p laterP, max h laterH, max m laterM, max s laterS, max n laterN, ?_⟩
  intro a b c d e enoughP enoughH enoughM enoughS enoughN
  simp only [done a b c d e (Nat.le_trans (Nat.le_max_left _ _) enoughP) (Nat.le_trans (Nat.le_max_left _ _) enoughH)
    (Nat.le_trans (Nat.le_max_left _ _) enoughM) (Nat.le_trans (Nat.le_max_left _ _) enoughS)
    (Nat.le_trans (Nat.le_max_left _ _) enoughN), Outcome.bind,
    nextDone a b c d e (Nat.le_trans (Nat.le_max_right _ _) enoughP) (Nat.le_trans (Nat.le_max_right _ _) enoughH)
      (Nat.le_trans (Nat.le_max_right _ _) enoughM) (Nat.le_trans (Nat.le_max_right _ _) enoughS)
      (Nat.le_trans (Nat.le_max_right _ _) enoughN)]

/-- Every completed projection graph supplies stable physical and read bounds. -/
theorem projection_complete [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {before : NativeState width Symbol Guard}
    {result : Value Symbol Guard} {heap : InternedConstructorTemplates.State Symbol Guard}
    (trace : SourceEqualityProjectionGraph.Forest path values before.machine.heap result heap) (memo : Memo Symbol Guard) :
    StableRun (fun p h _ _ _ => projection p h path values before memo) result (advanceHeap before heap) memo := by
  obtain ⟨p, h, stable⟩ := SourceEqualityProjectionWorkerComplete.forest_stable trace
  exact ⟨p, h, 0, 0, 0, by intro a b c d e enoughP enoughH _ _ _; simp only [projection, stable a b enoughP enoughH]⟩

/-- Every actual recursive merge supplies stable instruction and comparison bounds. -/
theorem merge_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {value result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : SourceCurrentMemoMergeNative.Merge clear top value before memo result after saved) :
    StableRun (fun _ _ m s _ => merge clear top m s value before memo) result after saved := by
  cases trace with
  | done actual =>
      obtain ⟨m, s, stable⟩ := SourceCurrentMemoMergeWorkerProofs.call_complete actual
      exact ⟨0, 0, m, s, 0, by intro p h a b n _ _ enoughM enoughS _; simp only [merge, stable a b enoughM enoughS]⟩

/-- Every completed operand graph supplies its stable actual projection-then-merge execution. -/
theorem operand_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {path : List Int} {values : List (Value Symbol Guard)}
    {result : Value Symbol Guard} {before after : NativeState width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) :
    StableRun (fun p h m s _ => operand clear top p h m s path values before memo) result after saved := by
  cases trace with
  | force projected merged => exact bind_stable _ _ _ _ _ _ _ _ (projection_complete projected memo) (merge_complete merged)

/-- A completed checked native request supplies its exact stable returned native state. -/
theorem leaf_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {value tail result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} (trace : Step emptyGuard conjoin value tail before result after) (memo : Memo Symbol Guard) :
    StableRun (fun _ _ _ _ n => leaf emptyGuard conjoin n value tail before memo) result after memo := by
  obtain ⟨bound, stable⟩ := trace.stable
  exact ⟨0, 0, 0, 0, bound, by intro p h m s n _ _ _ _ enough; simp only [leaf, stable n enough]⟩

/-- Every actual fold supplies stable bounds with its precise returned native and merge tables. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved) :
    StableRun (fun p h m s n => fold emptyGuard conjoin clear top p h m s n values seed paths before memo) result after saved := by
  induction trace with
  | nil seed => exact operand_complete seed
  | cons operand rest step ih =>
      exact bind_stable _ _ _ _ _ _ _ _ (operand_complete operand)
        (bind_stable _ _ _ _ _ _ _ _ ih (leaf_complete step _))

/-- Every actual first-seeded target graph supplies stable finite execution at all larger bounds. -/
theorem target_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before memo result after saved) :
    StableRun (fun p h m s n => target emptyGuard conjoin clear top p h m s n values paths before memo) result after saved := by
  cases trace with
  | nil => exact ⟨0, 0, 0, 0, 0, by intros; rfl⟩
  | cons actual => exact fold_complete actual

end MicroCFTA.SourceCurrentMemoTargetWorkerProofs
