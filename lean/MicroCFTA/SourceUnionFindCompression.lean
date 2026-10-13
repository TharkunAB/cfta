import MicroCFTA.UnionFind

/-!
# Conditional path-compression writes

The source writes the current parent entry only when its old parent differs
from the final representative. Compression uses the state returned by the
recursive call. This worker has the same representative, stored size, and
entire extensional forest as the earlier unconditional-write worker.
The finite bound remains an execution witness, not a source failure mode.
-/

namespace MicroCFTA.SourceUnionFindCompression

open UnionFind

/-- Writing an already present entry leaves every map lookup unchanged. -/
theorem put_present (forest : Forest) (uv : Nat) (entry : Entry)
    (present : forest uv = some entry) : put forest uv entry = forest := by
  funext other
  by_cases same : other = uv
  · subst other; simp [put, present]
  · simp [put, same]

/-- Looking up an existing direct root cannot change its child's parent entry. -/
theorem direct_parent_unchanged (fuel : Nat) (forest : Forest) (uv parent : Nat) (found : Result)
    (child : forest uv = some (.parent parent))
    (completed : UnionFind.findRoot fuel forest parent = some found)
    (same : found.representative = parent) : found.forest uv = some (.parent parent) := by
  have terminal := reaches_terminal (UnionFind.findRoot_correct fuel forest parent found completed).1
  rw [same] at terminal
  cases fuel with
  | zero => simp [UnionFind.findRoot] at completed
  | succ fuel =>
      cases rootEntry : forest parent with
      | none =>
          have different : uv ≠ parent := by intro equal; subst uv; simp [rootEntry] at child
          simp [UnionFind.findRoot, rootEntry] at completed
          subst found
          simp [put, different, child]
      | some storedEntry =>
          cases storedEntry with
          | root size =>
              simp [UnionFind.findRoot, rootEntry] at completed
              subst found
              exact child
          | parent next => simp [UnionFind.read, rootEntry] at terminal

/-- The optimized source lookup skips a parent write that already has its final value. -/
def findRoot : Nat → Forest → Nat → Option Result
  | 0, _, _ => none
  | fuel + 1, forest, uv =>
      match forest uv with
      | none => some ⟨uv, 1, put forest uv (.root 1)⟩
      | some (.root size) => some ⟨uv, size, forest⟩
      | some (.parent parent) => do
          let found ← findRoot fuel forest parent
          if parent = found.representative then some found
          else some {found with forest := put found.forest uv (.parent found.representative)}

/-- Conditional writes preserve the complete earlier lookup result, at every bound. -/
theorem findRoot_eq (fuel : Nat) (forest : Forest) (uv : Nat) :
    findRoot fuel forest uv = UnionFind.findRoot fuel forest uv := by
  induction fuel generalizing forest uv with
  | zero => rfl
  | succ fuel ih =>
      cases lookup : forest uv with
      | none => simp [findRoot, UnionFind.findRoot, lookup]
      | some storedEntry =>
          cases storedEntry with
          | root size => simp [findRoot, UnionFind.findRoot, lookup]
          | parent parent =>
              simp only [findRoot, UnionFind.findRoot, lookup, ih]
              cases recursive : UnionFind.findRoot fuel forest parent with
              | none => rfl
              | some found =>
                  simp only [Bind.bind, Option.bind]
                  by_cases same : parent = found.representative
                  · have present := direct_parent_unchanged fuel forest uv parent found lookup recursive same.symm
                    have writeSame := put_present found.forest uv (.parent parent) present
                    simp only [same] at writeSame
                    simp [same, writeSame]
                  · simp [same]

/-- Successful optimized lookup follows the same original path and preserves every path. -/
theorem findRoot_correct (fuel : Nat) (forest : Forest) (uv : Nat) (found : Result)
    (completed : findRoot fuel forest uv = some found) :
    Reaches forest uv found.representative found.size ∧
      (∀ {other root size}, Reaches forest other root size → Reaches found.forest other root size) := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_correct fuel forest uv found completed

/-- Every finite parent path gives a finite optimized source execution. -/
theorem findRoot_terminates (path : Reaches forest uv representative size) :
    ∃ fuel found, findRoot fuel forest uv = some found := by
  obtain ⟨fuel, found, completed⟩ := UnionFind.findRoot_terminates path
  exact ⟨fuel, found, by rw [findRoot_eq]; exact completed⟩

/-- Additional recursion fuel leaves an optimized successful result unchanged. -/
theorem findRoot_moreFuel (fuel extra : Nat) (forest : Forest) (uv : Nat) (found : Result)
    (completed : findRoot fuel forest uv = some found) :
    findRoot (fuel + extra) forest uv = some found := by
  rw [findRoot_eq] at completed ⊢
  exact UnionFind.findRoot_moreFuel fuel extra forest uv found completed

/-- Conditional writes preserve termination of every later lookup. -/
theorem findRoot_total (valid : Total forest)
    (completed : findRoot fuel forest uv = some found) : Total found.forest := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_total valid completed

/-- Conditional writes preserve exactly the existing union-find classes. -/
theorem findRoot_classes (valid : Total forest)
    (completed : findRoot fuel forest uv = some found) (left right : Nat) :
    SameClass found.forest left right ↔ SameClass forest left right := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_classes valid completed left right

/-- Conditional writes retain all correct stored class sizes. -/
theorem findRoot_sizes (valid : Total forest) (sizes : SizesCorrect forest domain)
    (completed : findRoot fuel forest uv = some found) : SizesCorrect found.forest domain := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_sizes valid sizes completed

/-- Conditional writes preserve all permitted assignments to equality variables. -/
theorem findRoot_satisfies (valid : Total forest)
    (completed : findRoot fuel forest uv = some found) (assignment : Nat → α) :
    Satisfies found.forest assignment ↔ Satisfies forest assignment := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_satisfies valid completed assignment

/-- The public find wrapper returns the representative and compressed state. -/
def find (fuel : Nat) (forest : Forest) (uv : Nat) : Option (Nat × Forest) :=
  (findRoot fuel forest uv).map fun found => (found.representative, found.forest)

/-- The optimized public wrapper has the identical representative and final map. -/
theorem find_eq (fuel : Nat) (forest : Forest) (uv : Nat) :
    find fuel forest uv = (UnionFind.findRoot fuel forest uv).map
      (fun found => (found.representative, found.forest)) := by rw [find, findRoot_eq]

/-- The source union uses conditional-write lookup before its unchanged size-based link. -/
def union (leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat) : Option Forest := do
  let first ← findRoot leftFuel forest left
  let second ← findRoot rightFuel first.forest right
  if first.representative = second.representative then some second.forest
  else if first.size < second.size then
    some (link second.forest first.representative second.representative first.size second.size)
  else some (link second.forest second.representative first.representative second.size first.size)

/-- Both compressed lookups preserve the complete existing union result. -/
theorem union_eq (leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat) :
    union leftFuel rightFuel forest left right = UnionFind.union leftFuel rightFuel forest left right := by
  simp only [union, UnionFind.union, findRoot_eq]

end MicroCFTA.SourceUnionFindCompression
