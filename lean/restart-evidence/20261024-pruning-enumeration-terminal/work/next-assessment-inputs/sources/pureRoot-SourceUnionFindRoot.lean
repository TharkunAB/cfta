import MicroCFTA.UnionFind

/-!
# Read-only source representative lookup

The source root function follows parent entries without compression.
The finite bound exposes execution. A successful lookup leaves the input
forest unchanged and returns the earlier findRoot representative.
-/
namespace MicroCFTA.SourceUnionFindRoot

open UnionFind

/-- Follow the source parent chain without constructing a replacement forest. -/
def root : Nat → Forest → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, forest, uv =>
      match forest uv with
      | some (.parent parent) => root fuel forest parent
      | _ => some uv

/-- Pure and compressing lookup return the same representative at each bound. -/
theorem root_eq (fuel : Nat) (forest : Forest) (uv : Nat) :
    root fuel forest uv = (UnionFind.findRoot fuel forest uv).map Result.representative := by
  induction fuel generalizing uv with
  | zero => rfl
  | succ fuel ih =>
      cases lookup : forest uv with
      | none => simp [root, UnionFind.findRoot, lookup]
      | some entry =>
          cases entry with
          | root size => simp [root, UnionFind.findRoot, lookup]
          | parent parent =>
              simp only [root, UnionFind.findRoot, lookup, ih]
              cases UnionFind.findRoot fuel forest parent <;> rfl

/-- Each returned source representative has an actual finite parent path. -/
theorem root_correct (fuel : Nat) (forest : Forest) (uv representative : Nat)
    (completed : root fuel forest uv = some representative) :
    ∃ size, Reaches forest uv representative size := by
  rw [root_eq] at completed
  cases lookup : UnionFind.findRoot fuel forest uv with
  | none => simp [lookup] at completed
  | some found =>
      have same : found.representative = representative := by simpa [lookup] using completed
      exact ⟨found.size, same ▸ (UnionFind.findRoot_correct fuel forest uv found lookup).1⟩

/-- Every finite parent path gives a successful pure execution. -/
theorem root_terminates (forest : Forest) (uv representative size : Nat)
    (path : Reaches forest uv representative size) :
    ∃ fuel, root fuel forest uv = some representative := by
  obtain ⟨fuel, found, completed⟩ := UnionFind.findRoot_terminates path
  have same := (reaches_unique (UnionFind.findRoot_correct fuel forest uv found completed).1 path).1
  exact ⟨fuel, by simp [root_eq, completed, same]⟩

/-- More fuel retains every successful pure representative result. -/
theorem root_moreFuel (fuel extra : Nat) (forest : Forest) (uv representative : Nat)
    (completed : root fuel forest uv = some representative) :
    root (fuel + extra) forest uv = some representative := by
  rw [root_eq] at completed ⊢
  cases lookup : UnionFind.findRoot fuel forest uv with
  | none => simp [lookup] at completed
  | some found =>
      rw [UnionFind.findRoot_moreFuel fuel extra forest uv found lookup]
      simpa [lookup] using completed

end MicroCFTA.SourceUnionFindRoot
