import MicroCFTA.EqualityFixedSaturationCounterexample

/-!
# The additional obligation for three peer paths

The binary projected-class proof uses commutative row intersection and
admitted diagonal rows. Those laws do not prove termination of the source
target fold for three paths. A three-element commutative idempotent algebra
has a three-pass cycle. This algebra is not a source intersection model.

The concrete source-style row algebra gives a different obstruction: a
three-path class can remove an endpoint row after its first pass. This
example converges. The public Haskell probe is
`/tmp/mcfta-projected-three-progress.hs`. Its exact source identities passed
in `/tmp/mcfta-projected-three-progress.log`.
-/
namespace MicroCFTA.EqualityFixedMultiplePeers

/-- Three endpoint projections read from the same snapshot. -/
abbrev Triple (Node : Type) := Node × Node × Node

/-- With three paths, each target is the intersection of the other two projections. -/
def round (meet : Node → Node → Node) (nodes : Triple Node) : Triple Node :=
  let (first, second, third) := nodes
  (meet first (meet second third), meet second (meet first third), meet third (meet first second))

/-- A finite commutative idempotent algebra need not behave like source intersection. -/
inductive Point where
  | a | b | c
  deriving DecidableEq

/-- Distinct points produce the third point. -/
def steiner : Point → Point → Point
  | .a, .a => .a
  | .b, .b => .b
  | .c, .c => .c
  | .a, .b | .b, .a => .c
  | .a, .c | .c, .a => .b
  | .b, .c | .c, .b => .a

/-- The two row laws used by the binary theorem both hold. -/
theorem steiner_laws : (∀ point, steiner point point = point) ∧
    (∀ first second, steiner first second = steiner second first) := by
  constructor
  · intro point; cases point <;> rfl
  · intro first second; cases first <;> cases second <;> rfl

/-- The synchronized three-peer fold has a nontrivial cycle under those two laws alone. -/
theorem steiner_cycle :
    round steiner (.a, .a, .b) = (.b, .b, .c) ∧
    round steiner (.b, .b, .c) = (.c, .c, .a) ∧
    round steiner (.c, .c, .a) = (.a, .a, .b) := by decide +kernel

/-- Commutativity and idempotence alone cannot supply a strict rank for this schedule. -/
theorem no_ci_rank : ¬ ∃ rank : Triple Point → Nat,
    ∀ before, round steiner before ≠ before → rank (round steiner before) < rank before := by
  rintro ⟨rank, decreases⟩
  have first := decreases (.a, .a, .b) (by decide +kernel)
  have second := decreases (.b, .b, .c) (by decide +kernel)
  have third := decreases (.c, .c, .a) (by decide +kernel)
  rw [steiner_cycle.1] at first
  rw [steiner_cycle.2.1] at second
  rw [steiner_cycle.2.2] at third
  omega

open EqualityFixedSaturationCounterexample

/-- Three unary endpoints over the canonical four-atom source witness. -/
def sourceInitial : Triple (List (List Nat)) := ([a], [a], [b])

/-- The first pass gives different row representations to the third peer. -/
theorem source_first : round parentMeet sourceInitial = ([w], [w], [z]) := by decide +kernel

/-- The second pass replaces the third peer's row and then reaches a fixed point. -/
theorem source_second : round parentMeet ([w], [w], [z]) = ([w], [w], [w]) ∧
    round parentMeet ([w], [w], [w]) = ([w], [w], [w]) := by decide +kernel

/-- Pointwise row retention after the first pass does not extend from two peers to three. -/
theorem source_post_first_deletes_row :
    z ∈ (round parentMeet sourceInitial).2.2 ∧
      z ∉ (round parentMeet (round parentMeet sourceInitial)).2.2 := by decide +kernel

end MicroCFTA.EqualityFixedMultiplePeers
