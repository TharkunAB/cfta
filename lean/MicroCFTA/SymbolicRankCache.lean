import MicroCFTA.SymbolicRankSoundness

/-!
# Inverse ranking preserves count caches on acceptance and rejection

The inverse can return `Nothing` after several successful count calls.
Those calls still leave a correct cache. The singleton worker restores its
snapshot. Thus a rejected term can safely share counts with later calls.
-/
namespace MicroCFTA.SymbolicDriver

/-- Successful state actions retain a chosen cache invariant. -/
def Preserves (invariant : State → Prop) (action : StateT State (Except Failure) Value) : Prop :=
  ∀ before result after, invariant before → action before = .ok (result, after) → invariant after

/-- Returning a value leaves the invariant unchanged. -/
theorem preserves_pure (invariant : State → Prop) (value : Value) :
    Preserves invariant (pure value : StateT State (Except Failure) Value) := by
  intro before result after valid success
  cases success
  exact valid

/-- A failed action has no successful state to invalidate. -/
theorem preserves_error (invariant : State → Prop) (error : Failure) :
    Preserves invariant (throw error : StateT State (Except Failure) Value) := by
  intro before result after valid success
  cases success

/-- Sequential state actions retain the invariant at their intermediate cache. -/
theorem preserves_bind (invariant : State → Prop) (first : StateT State (Except Failure) Input)
    (rest : Input → StateT State (Except Failure) Value)
    (safeFirst : Preserves invariant first) (safeRest : ∀ value, Preserves invariant (rest value)) :
    Preserves invariant (first >>= rest) := by
  intro before result after valid success
  change Except.bind (first before) (fun (value, middle) => rest value middle) = .ok (result, after) at success
  cases firstRun : first before with
  | error error => simp only [firstRun, Except.bind] at success; cases success
  | ok pair =>
    rcases pair with ⟨value, middle⟩
    exact safeRest value middle result after (safeFirst before value middle valid firstRun)
      (by simpa only [firstRun, Except.bind] using success)

/-- Snapshot isolation preserves every invariant of the original cache. -/
theorem isolated_preserves (invariant : Counts Symbol → Prop) (action : CountM Symbol Value) :
    Preserves invariant (isolated action) := by
  intro before result after valid success
  obtain ⟨_, _, rfl⟩ := isolated_inner action before after result success
  exact valid

/-- Exact semantic counting preserves the invariant on every completed count. -/
theorem count_preserves [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (size : Nat → Nat) (invariant : Counts Symbol → Prop) (sound : CountSound graph size invariant)
    (fuel root : Nat) : Preserves invariant (countNode graph fuel root) := by
  intro before count after valid success
  exact (sound fuel root before count after valid success).2

/-- All three inverse workers preserve valid count snapshots, including rejected terms. -/
theorem ranking_preserves [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph size invariant) (fuel : Nat) :
    (∀ root path term before, Preserves invariant (rankAt graph order fuel root path term before)) ∧
    (∀ root path wanted children before available,
      Preserves invariant (rankConstructor graph order fuel root path wanted children before available)) ∧
    (∀ root path before children, Preserves invariant (rankChildren graph order fuel root path before children)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro root path term before; exact preserves_error invariant _
    · intro root path wanted children before available; exact preserves_error invariant _
    · intro root path before children
      cases children with
      | nil => exact preserves_pure invariant _
      | cons child rest => exact preserves_error invariant _
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro root path term before
      cases term with
      | node symbol children =>
        apply preserves_bind invariant (countNode graph fuel (graph.project path root)) _
          (count_preserves graph size invariant sound fuel (graph.project path root))
        intro count
        by_cases singleton : count = 1
        · simp only [singleton, ↓reduceIte]
          exact preserves_bind invariant (isolated (selectUnique graph order fuel (graph.project path root) [])) _
            (isolated_preserves invariant _) (fun _ => preserves_pure invariant _)
        · simp only [singleton, ↓reduceIte]
          split
          · exact ih.2.1 root path (symbol, children.length) children before (constructorsAt graph order path root)
          · exact preserves_pure invariant _
    · intro root path wanted children before available
      cases available with
      | nil => exact preserves_pure invariant _
      | cons constructor rest =>
        apply preserves_bind invariant (countNode graph fuel (graph.condition path constructor root)) _
          (count_preserves graph size invariant sound fuel (graph.condition path constructor root))
        intro count
        split
        · split
          · exact preserves_pure invariant _
          · exact ih.2.2 (graph.condition path constructor root) path before children.zipIdx
        · exact ih.2.1 root path wanted children (before + count) rest
    · intro root path before children
      cases children with
      | nil => exact preserves_pure invariant _
      | cons child rest =>
        rcases child with ⟨term, index⟩
        apply preserves_bind invariant (rankAt graph order fuel root (path ++ [index]) term before) _
          (ih.1 root (path ++ [index]) term before)
        intro result
        cases result with
        | none => exact preserves_pure invariant _
        | some pair => exact ih.2.2 pair.1 path pair.2 rest

end MicroCFTA.SymbolicDriver
