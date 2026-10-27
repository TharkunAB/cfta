import MicroCFTA.UnionFind

/-!
# Union-find with direct parent pointers

This model follows the member-set backend in `Internal/UnionFind.hs`.
Lists describe finite set membership. Their order does not describe `IntSet`.
The map interface and natural-number identifiers remain abstract.
-/

namespace MicroCFTA.FlatUnionFind

/-- A direct parent pointer or a root with its size and members. -/
inductive Entry where
  | parent (uv : Nat)
  | root (size : Nat) (members : List Nat)
deriving DecidableEq, Repr

/-- The persistent map interface permits absent singleton roots. -/
abbrev Forest := Nat → Option Entry

/-- Replace one map entry. -/
def put (forest : Forest) (uv : Nat) (entry : Entry) : Forest :=
  fun other => if other = uv then some entry else forest other

/-- Read one parent pointer, or return the variable itself. -/
def root (forest : Forest) (uv : Nat) : Nat :=
  match forest uv with
  | some (.parent parent) => parent
  | _ => uv

/-- Read root metadata, with the source singleton default. -/
def entryOf (forest : Forest) (uv : Nat) : Nat × List Nat :=
  match forest uv with
  | some (.root size members) => (size, members)
  | _ => (1, [uv])

/-- Find reads the representative and retains the same forest. -/
def find (forest : Forest) (uv : Nat) : Nat × Forest :=
  (root forest uv, forest)

/-- Each supplied variable is a singleton root. Duplicate inputs have no effect. -/
def withInitialValues (variables : List Nat) : Forest :=
  fun uv => if uv ∈ variables then some (.root 1 [uv]) else none

/-- Parents target stored roots. Root metadata describes the complete class. -/
structure Valid (forest : Forest) : Prop where
  parents : ∀ uv parent, forest uv = some (.parent parent) →
    ∃ size members, forest parent = some (.root size members)
  roots : ∀ representative size members,
    forest representative = some (.root size members) →
    members.Nodup ∧ size = members.length ∧
      ∀ uv, uv ∈ members ↔ root forest uv = representative

/-- Every representative is a fixed point of the direct root read. -/
theorem root_root (valid : Valid forest) (uv : Nat) :
    root forest (root forest uv) = root forest uv := by
  cases lookup : forest uv with
  | none => simp [root, lookup]
  | some entry =>
    cases entry with
    | root size members => simp [root, lookup]
    | parent parent =>
      obtain ⟨size, members, terminal⟩ := valid.parents uv parent lookup
      simp [root, lookup, terminal]

/-- Root metadata also describes an absent singleton root exactly. -/
theorem entryOf_spec (valid : Valid forest)
    (fixed : root forest representative = representative) :
    (entryOf forest representative).2.Nodup ∧
      (entryOf forest representative).1 = (entryOf forest representative).2.length ∧
      ∀ uv, uv ∈ (entryOf forest representative).2 ↔
        root forest uv = representative := by
  cases lookup : forest representative with
  | none =>
    simp only [entryOf, lookup]
    refine ⟨by simp, by simp, ?_⟩
    intro uv
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact fixed
    · intro same
      cases actual : forest uv with
      | none => simpa [root, actual] using same
      | some entry =>
        cases entry with
        | root size members => simpa [root, actual] using same
        | parent parent =>
          have parentSame : parent = representative := by simpa [root, actual] using same
          obtain ⟨size, members, terminal⟩ := valid.parents uv parent actual
          rw [parentSame, lookup] at terminal
          contradiction
  | some entry =>
    cases entry with
    | root size members =>
      simpa only [entryOf, lookup] using valid.roots representative size members lookup
    | parent parent =>
      have same : parent = representative := by simpa [root, lookup] using fixed
      obtain ⟨size, members, terminal⟩ := valid.parents representative parent lookup
      rw [same, lookup] at terminal
      contradiction

/-- Initialization satisfies the direct-parent and complete-member invariant. -/
theorem initial_valid (variables : List Nat) : Valid (withInitialValues variables) := by
  have roots (uv : Nat) : root (withInitialValues variables) uv = uv := by
    simp [root, withInitialValues]
  refine ⟨?_, ?_⟩
  · intro uv parent lookup
    simp [withInitialValues] at lookup
    split at lookup <;> contradiction
  · intro representative size members lookup
    simp only [withInitialValues] at lookup
    split at lookup
    · cases lookup
      simpa [roots] using (show [representative].Nodup ∧ 1 = [representative].length ∧
        ∀ uv, uv ∈ [representative] ↔ uv = representative from ⟨by simp, rfl, by simp⟩)
    · contradiction

/-- Erase member lists to obtain the earlier parent-path interface. -/
def erase (forest : Forest) : UnionFind.Forest :=
  fun uv => (forest uv).map fun entry =>
    match entry with
    | .parent parent => .parent parent
    | .root size _ => .root size

/-- A direct representative is a root in the earlier path interface. -/
theorem erase_root (valid : Valid forest)
    (fixed : root forest representative = representative) :
    UnionFind.read (erase forest) representative =
      .root (entryOf forest representative).1 := by
  cases lookup : forest representative with
  | none => simp [UnionFind.read, erase, entryOf, lookup]
  | some entry =>
    cases entry with
    | root size members => simp [UnionFind.read, erase, entryOf, lookup]
    | parent parent =>
      have same : parent = representative := by simpa [root, lookup] using fixed
      obtain ⟨size, members, terminal⟩ := valid.parents representative parent lookup
      rw [same, lookup] at terminal
      contradiction

/-- Direct lookup gives the same representative and size as a finite parent path. -/
theorem erase_reaches (valid : Valid forest) (uv : Nat) :
    UnionFind.Reaches (erase forest) uv (root forest uv)
      (entryOf forest (root forest uv)).1 := by
  have terminal := erase_root valid (root_root valid uv)
  cases lookup : forest uv with
  | none =>
    simpa only [root, lookup] using (UnionFind.Reaches.root terminal)
  | some entry =>
    cases entry with
    | root size members =>
      simpa only [root, lookup] using (UnionFind.Reaches.root terminal)
    | parent parent =>
      apply UnionFind.Reaches.parent (by simp [UnionFind.read, erase, lookup])
      exact .root terminal

/-- Redirect every listed member to the selected winner. -/
def redirectMembers (forest : Forest) (winner : Nat) (members : List Nat) : Forest :=
  members.foldl (fun current uv => put current uv (.parent winner)) forest

/-- The redirect fold changes exactly the listed keys, even with duplicate inputs. -/
theorem redirectMembers_lookup (forest : Forest) (winner : Nat) (members : List Nat)
    (uv : Nat) :
    redirectMembers forest winner members uv =
      if uv ∈ members then some (.parent winner) else forest uv := by
  induction members generalizing forest with
  | nil => simp [redirectMembers]
  | cons head tail ih =>
    simp only [redirectMembers, List.foldl_cons]
    change redirectMembers (put forest head (.parent winner)) winner tail uv = _
    rw [ih]
    by_cases inTail : uv ∈ tail
    · simp [inTail]
    · simp [inTail, put]

/-- Redirect the losing class, then replace the winning root metadata. -/
def merge (forest : Forest) (winner winnerSize loserSize : Nat)
    (loserMembers winnerMembers : List Nat) : Forest :=
  put (redirectMembers forest winner loserMembers) winner
    (.root (winnerSize + loserSize) (loserMembers ++ winnerMembers))

/-- The complete merge has one root write and one member-redirection fold. -/
theorem merge_lookup (forest : Forest) (winner winnerSize loserSize : Nat)
    (loserMembers winnerMembers : List Nat) (uv : Nat) :
    merge forest winner winnerSize loserSize loserMembers winnerMembers uv =
      if uv = winner then some (.root (winnerSize + loserSize) (loserMembers ++ winnerMembers))
      else if uv ∈ loserMembers then some (.parent winner) else forest uv := by
  simp only [merge, put, redirectMembers_lookup]

end MicroCFTA.FlatUnionFind
