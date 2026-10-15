import MicroCFTA.SourceEqualityDemandTargetWorkerSound

/-!
# Stable finite execution of demanded source target graphs

Every completed demand graph supplies four finite proof bounds. Every
larger bound quadruple returns the identical target and full native state.
The bounds retain actual projection, merge, and native request order.
-/
namespace MicroCFTA.SourceEqualityDemandTargetWorkerComplete
open InternedConstructorTemplates SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityDemandTarget
open SourceEqualityDemandTargetWorker

/-- All larger independent bound quadruples return the identical completed value and full native state. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Result width Symbol Guard A) (result : A) (after : NativeState width Symbol Guard) : Prop :=
  ∃ projection head comparison native, ∀ p h c n, projection ≤ p → head ≤ h → comparison ≤ c → native ≤ n → evaluation p h c n = .done result after

/-- Two stable stages combine their four independent bounds at the literal intermediate state. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Result width Symbol Guard A)
    (next : Nat → Nat → Nat → Nat → A → NativeState width Symbol Guard → Result width Symbol Guard B)
    (value : A) (middle : NativeState width Symbol Guard) (result : B) (after : NativeState width Symbol Guard)
    (one : StableRun first value middle) (two : StableRun (fun p h c n => next p h c n value middle) result after) :
    StableRun (fun p h c n => (first p h c n).bind (next p h c n)) result after := by
  obtain ⟨p, h, c, n, done⟩ := one
  obtain ⟨laterP, laterH, laterC, laterN, nextDone⟩ := two
  refine ⟨max p laterP, max h laterH, max c laterC, max n laterN, ?_⟩
  intro a b d e enoughP enoughH enoughC enoughN
  simp only [done a b d e (Nat.le_trans (Nat.le_max_left _ _) enoughP) (Nat.le_trans (Nat.le_max_left _ _) enoughH)
    (Nat.le_trans (Nat.le_max_left _ _) enoughC) (Nat.le_trans (Nat.le_max_left _ _) enoughN), Result.bind,
    nextDone a b d e (Nat.le_trans (Nat.le_max_right _ _) enoughP) (Nat.le_trans (Nat.le_max_right _ _) enoughH)
      (Nat.le_trans (Nat.le_max_right _ _) enoughC) (Nat.le_trans (Nat.le_max_right _ _) enoughN)]

/-- A complete actual projection graph stabilizes its native wrapper and identical returned heap. -/
theorem projection_stable [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {before : NativeState width Symbol Guard} {result : Value Symbol Guard}
    {heap : InternedConstructorTemplates.State Symbol Guard} (trace : SourceEqualityProjectionGraph.Forest path values before.machine.heap result heap) :
    StableRun (fun p h _ _ => projection p h path values before) result (advanceHeap before heap) := by
  obtain ⟨p, h, stable⟩ := SourceEqualityProjectionWorkerComplete.forest_stable trace
  refine ⟨p, h, 0, 0, ?_⟩
  intro a b c d enoughP enoughH _ _
  simp only [projection, stable a b enoughP enoughH]

/-- A complete actual merge receipt stabilizes its native wrapper without resetting memo tables. -/
theorem merge_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {value result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (trace : SourceEqualityNativeMerge.Merge clear top value before result after) :
    StableRun (fun _ _ c _ => merge clear top c value before) result after := by
  cases trace with
  | done bound actual =>
      rename_i heap
      refine ⟨0, 0, bound, 0, ?_⟩
      intro p h c n _ _ enough _
      have repeated := SourceMergedStability.worker_refines MergedSourceGrouping.groups clear top
        (MergedOrdinaryHeight.height value) (MergedOrdinaryHeight.height value) (Nat.le_refl _) bound (c - bound)
        value before.machine.heap result _ actual
      have stable : SourceMergedWorker.execute clear top c value before.machine.heap = .done result heap := by
        simpa only [SourceMergedWorker.execute, Nat.add_sub_of_le enough] using repeated
      simp only [merge, stable]

/-- Every complete actual demanded operand supplies stable projection, read, and comparison bounds. -/
theorem operand_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} (trace : Operand clear top path values before result after) :
    StableRun (fun p h c _ => operand clear top p h c path values before) result after := by
  cases trace with
  | force projected merged => exact bind_stable _ _ _ _ _ _ (projection_stable projected) (merge_stable merged)

/-- Every complete native request supplies its exact stable request bound. -/
theorem leaf_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {value tail result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} (trace : Step emptyGuard conjoin value tail before result after) :
    StableRun (fun _ _ _ n => leaf emptyGuard conjoin n value tail before) result after := by
  obtain ⟨bound, stable⟩ := trace.stable
  refine ⟨0, 0, 0, bound, ?_⟩
  intro p h c n _ _ _ enough
  simp only [leaf, stable n enough]

/-- A complete interleaved source fold supplies stable identical target and full native state. -/
theorem fold_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} (trace : Fold emptyGuard conjoin clear top values seed paths before result after) :
    StableRun (fun p h c n => fold emptyGuard conjoin clear top p h c n values seed paths before) result after := by
  induction trace with
  | nil seed => exact operand_stable seed
  | cons operand rest step ih => exact bind_stable _ _ _ _ _ _ (operand_stable operand) (bind_stable _ _ _ _ _ _ ih (leaf_stable step))

/-- Every complete empty or first-seeded source target has stable finite execution at all larger bound quadruples. -/
theorem target_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard} (trace : Target emptyGuard conjoin clear top values paths before result after) :
    StableRun (fun p h c n => target emptyGuard conjoin clear top p h c n values paths before) result after := by
  cases trace with
  | nil => exact ⟨0, 0, 0, 0, by intros; rfl⟩
  | cons fold => exact fold_stable fold

end MicroCFTA.SourceEqualityDemandTargetWorkerComplete
