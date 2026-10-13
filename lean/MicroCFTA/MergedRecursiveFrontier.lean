import Std

/-!
# Historical repeated recursive-frontier expansion

Before the retained-union repair, the five recursive operands produced an
ordinary child union. Later equality passes entered that union again. The
source replay verifies the equations below through round twelve. This module
proves growth for every round of the explicit frontier model. The intersection
rules record the relevant unary Cartesian cases and the closed Mu pair table;
they are not an extraction proof for the complete interned intersection worker.
-/
namespace MicroCFTA.MergedRecursiveFrontier

/-- Ordinary records above the five fixed productive binders and one empty binder. -/
inductive Spine where
  | loop (label : Fin 5)
  | dead
  | unary (child : Spine)
  | branch (label : Fin 5) (main extra : Spine)
  deriving DecidableEq, Repr

/-- The number of ordinary levels before an opaque recursive binder. -/
def height : Spine → Nat
  | .loop _ | .dead => 0
  | .unary child => height child + 1
  | .branch _ main extra => max (height main) (height extra) + 1

/-- The empty binder gains one ordinary unary prefix at each historical pass. -/
def deadPrefix : Nat → Spine
  | 0 => .dead
  | rounds + 1 => .unary (deadPrefix rounds)

/-- One productive branch retains its base leaf and both recursive intersections. -/
def branch : Nat → Fin 5 → Spine
  | 0, label => .loop label
  | rounds + 1, label => .branch label (branch rounds label) (deadPrefix rounds)

/-- Unary source intersection with the corresponding exposed merged context.
The base pair table retains an equal productive binder and uses the empty
binder for unequal productive binders. Duplicate empty results have one key. -/
inductive MeetsContext : Nat → Spine → Spine → Prop where
  | loop : MeetsContext 0 (.loop label) (.branch label (.loop label) .dead)
  | dead : MeetsContext 0 .dead (.unary .dead)
  | unary : MeetsContext rounds before after →
      MeetsContext (rounds + 1) (.unary before) (.unary after)
  | branch : MeetsContext rounds left leftResult → MeetsContext rounds right rightResult →
      MeetsContext (rounds + 1) (.branch label left right) (.branch label leftResult rightResult)

/-- The empty branch follows its next explicit frontier by unary Cartesian intersection. -/
theorem dead_step (rounds : Nat) : MeetsContext rounds (deadPrefix rounds) (deadPrefix (rounds + 1)) := by
  induction rounds with
  | zero => exact .dead
  | succ rounds ih => exact .unary ih

/-- Each productive branch reaches its next frontier through the individual source row rules. -/
theorem branch_step (rounds : Nat) (label : Fin 5) :
    MeetsContext rounds (branch rounds label) (branch (rounds + 1) label) := by
  induction rounds with
  | zero => exact .loop
  | succ rounds ih => exact .branch ih (dead_step rounds)

/-- Both equality peers retain the same five productive alternatives. -/
def frontier (rounds : Nat) : Fin 5 → Spine := branch rounds

/-- One fixed binary equality class updates all five endpoint alternatives. -/
def Round (rounds : Nat) (before after : Fin 5 → Spine) : Prop :=
  ∀ label, MeetsContext rounds (before label) (after label)

/-- The model follows one fixed schedule, with equal input peers at every pass. -/
theorem frontier_step (rounds : Nat) : Round rounds (frontier rounds) (frontier (rounds + 1)) :=
  branch_step rounds

/-- Every empty prefix has exactly its number of ordinary unary records. -/
theorem dead_height (rounds : Nat) : height (deadPrefix rounds) = rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simp [deadPrefix, height, ih]

/-- Every historical round adds an ordinary level above each productive binder. -/
theorem branch_height (rounds : Nat) (label : Fin 5) : height (branch rounds label) = rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simp [branch, height, ih, dead_height]

/-- No round of the explicit fixed-schedule frontier model is an identity fixed point. -/
theorem frontier_not_fixed (rounds : Nat) : frontier (rounds + 1) ≠ frontier rounds := by
  intro same
  have heights := congrArg (fun values => height (values (0 : Fin 5))) same
  simp only [frontier, branch_height] at heights
  omega

/-- Read a unary term by its number of f constructors and its final base label. -/
def Accepts : Spine → Nat → Fin 5 → Prop
  | .loop expected, _, actual => actual = expected
  | .dead, _, _ => False
  | .unary _, 0, _ => False
  | .unary child, depth + 1, label => Accepts child depth label
  | .branch expected _ _, 0, actual => actual = expected
  | .branch _ main extra, depth + 1, label => Accepts main depth label ∨ Accepts extra depth label

/-- Every added empty frontier still rejects all finite terms. -/
theorem dead_rejects (rounds depth : Nat) (label : Fin 5) : ¬Accepts (deadPrefix rounds) depth label := by
  induction rounds generalizing depth with
  | zero => simp [deadPrefix, Accepts]
  | succ rounds ih => cases depth <;> simp [deadPrefix, Accepts, ih]

/-- The ordinary prefixes change identities but preserve each productive binder's finite language. -/
theorem branch_language (rounds depth : Nat) (expected actual : Fin 5) :
    Accepts (branch rounds expected) depth actual ↔ actual = expected := by
  induction rounds generalizing depth with
  | zero => rfl
  | succ rounds ih => cases depth <;> simp [branch, Accepts, ih, dead_rejects]

/-- Every model frontier retains exactly the five original unary languages. -/
theorem frontier_language (rounds depth : Nat) (label : Fin 5) :
    ∃ index, Accepts (frontier rounds index) depth label :=
  ⟨label, (branch_language rounds depth label label).mpr rfl⟩

end MicroCFTA.MergedRecursiveFrontier
