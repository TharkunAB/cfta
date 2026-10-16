import MicroCFTA.SourceCurrentMemoSharedLeafWorker
import MicroCFTA.SourceCurrentMemoTargetWorkerProofs

/-!
# Exact graph correspondence and stable shared leaf bounds

Successful workers derive the actual new force and leaf graphs. Completed
finite graphs supply five independent sufficient bounds. Every larger
bound returns the same value and complete native, target, and merge state.
-/
namespace MicroCFTA.SourceCurrentMemoSharedLeafWorkerProofs
open InternedConstructorTemplates SourceCurrentMemoSharedTargetState
open SourceCurrentMemoSharedTargetForce SourceCurrentMemoSharedTargetLeaf SourceCurrentMemoSharedLeafWorker

/-- A completed sequence contains its exact returned prefix and continuation state. -/
theorem bind_done_iff (first : Outcome width Symbol Guard A)
    (next : A → State width Symbol Guard → Outcome width Symbol Guard B) (value : B) (after : State width Symbol Guard) :
    first.bind next = .done value after ↔ ∃ input middle, first = .done input middle ∧ next input middle = .done value after := by
  cases first with
  | done input middle =>
      constructor
      · intro done; exact ⟨input, middle, rfl, done⟩
      · rintro ⟨_, _, same, done⟩; cases same; exact done
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, impossible, _⟩; cases impossible

/-- All larger projection, read, merge, selection, and native bounds retain the same complete result. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard A)
    (value : A) (after : State width Symbol Guard) : Prop :=
  ∃ projection read merge selection native, ∀ p h w c n,
    projection ≤ p → read ≤ h → merge ≤ w → selection ≤ c → native ≤ n → evaluation p h w c n = .done value after

/-- Two actual stages combine their five sufficient bounds at the literal returned state. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard A)
    (next : Nat → Nat → Nat → Nat → Nat → A → State width Symbol Guard → Outcome width Symbol Guard B)
    (value : A) (middle : State width Symbol Guard) (result : B) (after : State width Symbol Guard)
    (one : StableRun first value middle) (two : StableRun (fun p h w c n => next p h w c n value middle) result after) :
    StableRun (fun p h w c n => (first p h w c n).bind (next p h w c n)) result after := by
  obtain ⟨p, h, w, c, n, done⟩ := one
  obtain ⟨q, i, x, d, m, later⟩ := two
  refine ⟨max p q, max h i, max w x, max c d, max n m, ?_⟩
  intro a b e f g ep eh ew ec en
  simp only [done a b e f g (Nat.le_trans (Nat.le_max_left _ _) ep) (Nat.le_trans (Nat.le_max_left _ _) eh)
    (Nat.le_trans (Nat.le_max_left _ _) ew) (Nat.le_trans (Nat.le_max_left _ _) ec) (Nat.le_trans (Nat.le_max_left _ _) en),
    Outcome.bind, later a b e f g (Nat.le_trans (Nat.le_max_right _ _) ep) (Nat.le_trans (Nat.le_max_right _ _) eh)
      (Nat.le_trans (Nat.le_max_right _ _) ew) (Nat.le_trans (Nat.le_max_right _ _) ec) (Nat.le_trans (Nat.le_max_right _ _) en)]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))

/-- Successful checked forcing derives exact reuse or the actual new memo-aware target graph. -/
theorem force_graph (p h w c n : Nat) (path : EqualityNormalize.Path) (before : State width Symbol Guard)
    (value : Value Symbol Guard) (after : State width Symbol Guard)
    (ranges : ForceRanges emptyGuard conjoin clear top record originals path before)
    (done : force emptyGuard conjoin clear top p h w c n record originals path before = .done value after) :
    Force emptyGuard conjoin clear top record originals path before value after := by
  cases present : before.targets path with
  | some stored =>
      simp only [force, present] at done
      cases done
      exact .hit present
  | none =>
      cases actual : SourceCurrentMemoTargetWorker.target emptyGuard conjoin clear top p h w c n originals
          (SourceEqualityClassTarget.operandPaths record.paths path) before.native before.memo with
      | done result native saved =>
          simp only [force, present, actual] at done
          cases done
          exact .miss present (SourceCurrentMemoTargetWorkerProofs.target_sound emptyGuard conjoin clear top p h w c n originals
            (SourceEqualityClassTarget.operandPaths record.paths path) before.native before.memo
            (by simpa only [ForceRanges, present] using ranges) _ _ _ actual)
      | failed => simp only [force, present, actual] at done; cases done

/-- A successful native stage retains its actual checked request and exact returned shared state. -/
theorem step_graph (n : Nat) (target input : Value Symbol Guard) (before : State width Symbol Guard)
    (value : Value Symbol Guard) (after : State width Symbol Guard)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native)
    (done : step emptyGuard conjoin n target input before = .done value after) :
    ∃ native, SourceEqualityNativeScoped.Step emptyGuard conjoin target input before.native value native ∧ after = advance before native := by
  cases actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin n
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native with
  | done result native =>
      simp only [step, actual] at done
      cases done
      exact ⟨native, .done n ranges actual, rfl⟩
  | yielded | failed | blocked => simp only [step, actual] at done; cases done

/-- Successful checked leaves derive the actual new force followed by the reached native request. -/
theorem leaf_graph (p h w c n : Nat) (path : EqualityNormalize.Path) (input : Value Symbol Guard)
    (before : State width Symbol Guard) (value : Value Symbol Guard) (after : State width Symbol Guard)
    (ranges : LeafRanges emptyGuard conjoin clear top record originals path input before)
    (done : leaf emptyGuard conjoin clear top p h w c n record originals path input before = .done value after) :
    Leaf emptyGuard conjoin clear top record originals path input before value after := by
  obtain ⟨target, middle, first, last⟩ := (bind_done_iff _ _ value after).mp done
  have forced := force_graph emptyGuard conjoin clear top record originals p h w c n path before target middle ranges.force first
  obtain ⟨native, actual, rfl⟩ := step_graph emptyGuard conjoin n target input middle value after (ranges.step target middle forced) last
  exact .apply forced actual

/-- Completed force graphs derive sufficient bounds without a future result or callback premise. -/
theorem force_stable {path value before after}
    (trace : Force (width := width) emptyGuard conjoin clear top record originals path before value after) :
    StableRun (fun p h w c n => force emptyGuard conjoin clear top p h w c n record originals path before) value after := by
  cases trace with
  | hit present => exact ⟨0, 0, 0, 0, 0, by intros; simp only [force, present]⟩
  | miss absent actual =>
      obtain ⟨p, h, w, c, n, stable⟩ := SourceCurrentMemoTargetWorkerProofs.target_complete actual
      exact ⟨p, h, w, c, n, by intro a b d e f ep eh ew ec en; simp only [force, absent, stable a b d e f ep eh ew ec en]⟩

/-- The actual native request supplies its sufficient bound and retains all shared tables. -/
theorem step_stable {target input value : Value Symbol Guard} {before : State width Symbol Guard}
    {native : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (actual : SourceEqualityNativeScoped.Step (width := width) emptyGuard conjoin target input before.native value native) :
    StableRun (fun _ _ _ _ n => step emptyGuard conjoin n target input before) value (advance before native) := by
  obtain ⟨bound, stable⟩ := actual.stable
  refine ⟨0, 0, 0, 0, bound, ?_⟩
  intro p h w c n _ _ _ _ enough
  simp only [step, stable n enough]

/-- Completed leaves stabilize both stages with the same native state, target slots, and completed merge table. -/
theorem leaf_stable {path input value before after}
    (trace : Leaf (width := width) emptyGuard conjoin clear top record originals path input before value after) :
    StableRun (fun p h w c n => leaf emptyGuard conjoin clear top p h w c n record originals path input before) value after := by
  cases trace with
  | apply forced actual =>
      exact bind_stable _ _ _ _ _ _ (force_stable emptyGuard conjoin clear top record originals forced)
        (step_stable emptyGuard conjoin actual)

/-- Completed executable forcing is exactly the actual new force graph under its reached checks. -/
theorem force_done_iff {path value before after}
    (ranges : ForceRanges (width := width) emptyGuard conjoin clear top record originals path before) :
    (∃ p h w c n, force emptyGuard conjoin clear top p h w c n record originals path before = .done value after) ↔
      Force emptyGuard conjoin clear top record originals path before value after := by
  constructor
  · rintro ⟨p, h, w, c, n, done⟩
    exact force_graph emptyGuard conjoin clear top record originals p h w c n path before value after ranges done
  · intro actual
    obtain ⟨p, h, w, c, n, done⟩ := force_stable emptyGuard conjoin clear top record originals actual
    exact ⟨p, h, w, c, n, done p h w c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩

/-- Completed executable leaves are exactly their actual new graphs under the reached checks. -/
theorem leaf_done_iff {path input value before after}
    (ranges : LeafRanges (width := width) emptyGuard conjoin clear top record originals path input before) :
    (∃ p h w c n, leaf emptyGuard conjoin clear top p h w c n record originals path input before = .done value after) ↔
      Leaf emptyGuard conjoin clear top record originals path input before value after := by
  constructor
  · rintro ⟨p, h, w, c, n, done⟩
    exact leaf_graph emptyGuard conjoin clear top record originals p h w c n path input before value after ranges done
  · intro actual
    obtain ⟨p, h, w, c, n, done⟩ := leaf_stable emptyGuard conjoin clear top record originals actual
    exact ⟨p, h, w, c, n, done p h w c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩

end MicroCFTA.SourceCurrentMemoSharedLeafWorkerProofs
