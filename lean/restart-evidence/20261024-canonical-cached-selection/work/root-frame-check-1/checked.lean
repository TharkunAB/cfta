import MicroCFTA.EnumerationDriver


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

/-!
# Complete frames for enumeration path compression

The frame preserves every nonforest field and every root path with its size.
It makes no claim about equal lookup fuel in different forests.
-/

namespace MicroCFTA.EnumerationCompressionFrame
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

/-- Compression changes only the forest and preserves exact root paths. -/
structure Frame (before after : State Symbol Guard) : Prop where
  counter : after.counter = before.counter
  values : after.values = before.values
  obligations : after.obligations = before.obligations
  recursionAncestry : after.recursionAncestry = before.recursionAncestry
  expansionAncestry : after.expansionAncestry = before.expansionAncestry
  reaches : ∀ uv root size,
    UnionFind.Reaches after.representatives uv root size ↔
      UnionFind.Reaches before.representatives uv root size

/-- An unchanged state satisfies the complete frame. -/
theorem Frame.refl (state : State Symbol Guard) : Frame state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => Iff.rfl⟩

/-- Consecutive frames preserve the same fields and root paths. -/
theorem Frame.trans (left : Frame before middle) (right : Frame middle after) : Frame before after :=
  ⟨right.counter.trans left.counter, right.values.trans left.values,
    right.obligations.trans left.obligations, right.recursionAncestry.trans left.recursionAncestry,
    right.expansionAncestry.trans left.expansionAncestry,
    fun uv root size => (right.reaches uv root size).trans (left.reaches uv root size)⟩

/-- A complete frame preserves finite root paths for every variable. -/
theorem Frame.total (frame : Frame before after) (total : UnionFind.Total before.representatives) :
    UnionFind.Total after.representatives := by
  intro uv
  obtain ⟨root, size, path⟩ := total uv
  exact ⟨root, size, (frame.reaches uv root size).mpr path⟩

/-- A pure result changes no state field. -/
theorem pure_frame (value result : α) (before after : State Symbol Guard)
    (success : Success (pure value) before result after) : Frame before after := by
  obtain ⟨_, rfl⟩ := (success_pure value result before after).mp success
  exact .refl before

/-- Reading the complete state changes no field. -/
theorem get_frame (before after value : State Symbol Guard)
    (success : Success get before value after) : Frame before after := by
  obtain ⟨_, rfl⟩ := (get_success before after value).mp success
  exact .refl before

/-- The actual representative read preserves root identities and stored sizes. -/
theorem representative_frame (fuel uv root : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives)
    (success : Success (representative fuel uv) before root after) : Frame before after := by
  obtain ⟨found, lookup, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro other actual size
  exact UnionFind.findRoot_reaches_iff total lookup other actual size

/-- A successful value read retains the actual root, its size, and its slot. -/
theorem getValue_frame (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (total : UnionFind.Total before.representatives)
    (success : Success (getValue fuel uv) before value after) :
    Frame before after ∧ ∃ root size,
      UnionFind.Reaches before.representatives uv root size ∧
      UnionFind.Reaches after.representatives uv root size ∧ before.values[root]? = some value := by
  obtain ⟨found, lookup, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  obtain ⟨path, preserved⟩ := UnionFind.findRoot_correct fuel before.representatives uv found lookup
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, found.representative, found.size, path, preserved path, stored⟩
  intro other root size
  exact UnionFind.findRoot_reaches_iff total lookup other root size

/-- Resolving one suspended reference preserves the complete frame. -/
private theorem resolve_frame (fuel : Nat) (blocked result : List Nat) (sc : Suspended)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (resolve fuel blocked sc) before result after) : Frame before after := by
  unfold resolve at success
  obtain ⟨root, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
  exact (representative_frame fuel sc.var root before middle total reading).trans
    (pure_frame (root :: blocked) result middle after final)

/-- Scanning one value preserves every field outside the forest. -/
private theorem collect_frame (graph : Graph Symbol Guard) (fuel : Nat)
    (accumulator result : List Nat × List Nat) (entry : UVarValue Symbol × Nat)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (collect graph fuel accumulator entry) before result after) : Frame before after := by
  obtain ⟨candidates, blocked⟩ := accumulator
  obtain ⟨value, index⟩ := entry
  cases value with
  | eliminated | enumerated _ =>
      exact pure_frame (candidates, blocked) result before after success
  | unenumerated node scs =>
      unfold collect at success
      obtain ⟨blockedResult, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
      have step : ∀ sc ∈ scs, ∀ accumulator previous result next, Frame before previous →
          Success (resolve fuel accumulator sc) previous result next → Frame before next := by
        intro sc _ accumulator previous result next previousFrame reading
        exact previousFrame.trans
          (resolve_frame fuel accumulator result sc previous next (previousFrame.total total) reading)
      have middleFrame := foldlM_invariant (resolve fuel) (Frame before) scs step
        blocked blockedResult before middle (.refl before) traversed
      exact middleFrame.trans (pure_frame _ result middle after final)

/-- The complete actual scheduler scan changes only root-path representation. -/
theorem findExpandable_frame (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (total : UnionFind.Total before.representatives)
    (success : Success (findExpandable graph fuel) before result after) : Frame before after := by
  unfold findExpandable at success
  change Success (get >>= fun state => do
    let summary ← state.values.zipIdx.foldlM (collect graph fuel) ([], [])
    finishScan summary) before result after at success
  obtain ⟨current, readState, read, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨rfl, rfl⟩ := (get_success before readState current).mp read
  obtain ⟨summary, scanned, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
  have step : ∀ entry ∈ before.values.zipIdx, ∀ accumulator previous result next, Frame before previous →
      Success (collect graph fuel accumulator entry) previous result next → Frame before next := by
    intro entry _ accumulator previous result next previousFrame scanning
    exact previousFrame.trans
      (collect_frame graph fuel accumulator result entry previous next (previousFrame.total total) scanning)
  have scannedFrame := foldlM_invariant (collect graph fuel) (Frame before) before.values.zipIdx step
    ([], []) summary before scanned (.refl before) traversed
  obtain ⟨_, rfl⟩ := (finishScan_success summary scanned after result).mp final
  exact scannedFrame

end MicroCFTA.EnumerationCompressionFrame
