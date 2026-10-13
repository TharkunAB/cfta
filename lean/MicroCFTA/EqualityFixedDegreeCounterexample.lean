import MicroCFTA.EqualityFixedSaturationCounterexample

/-!
# Mutual narrowing does not make source intersection associative

Five opaque guard atoms give a concrete family of canonical leaf domains.
The degree-n domain contains each nonempty conjunction of at most n atoms.
The public source probe `/tmp/mcfta-source-scc-nonassoc.hs` confirms the
complete leaf table and the nested identities checked below.

These are arbitrary-operand paths. They do not establish a cycle of one
fixed equality schedule.
-/
namespace MicroCFTA.EqualityFixedDegreeCounterexample
open EqualityFixedSaturationCounterexample

/-- Count the selected atoms of a five-bit conjunction mask. -/
def atoms (mask : Nat) : Nat :=
  ((List.range 5).map fun bit => if mask &&& (2 ^ bit) = 0 then 0 else 1).sum

/-- Keep every nonempty conjunction up to the selected degree. -/
def degree (bound : Nat) : List Nat := (List.range' 1 31).filter (fun mask => atoms mask ≤ bound)

/-- The two extremes of the five-atom domain family. -/
def first : List (List Nat) := canonical [degree 1, degree 5]

/-- Add the degree-three leaf between the two retained extremes. -/
def second : List (List Nat) := canonical [degree 1, degree 3, degree 5]

/-- The first return step retains the degree-four leaf. -/
def middle : List (List Nat) := canonical [degree 1, degree 4, degree 5]

/-- The expanding operand adds the degree-two leaf to the degree-one leaf. -/
def expanding : List (List Nat) := canonical [degree 1, degree 2]

/-- The narrow operand retains only the original degree-one leaf. -/
def original : List (List Nat) := [degree 1]

/-- Distinct leaf domains add their degree, capped at five. Identity preserves the degree. -/
theorem degree_table : ∀ first second : Fin 5,
    leafMeet (degree (first.val + 1)) (degree (second.val + 1)) =
      degree (if first = second then first.val + 1 else min 5 (first.val + second.val + 2)) := by
  decide +kernel

/-- Both nested nodes lie in one mutual-narrowing component. -/
theorem mutual_paths : parentMeet first expanding = second ∧
    parentMeet second original = middle ∧ parentMeet middle original = first := by decide +kernel

/-- Associativity fails even when all three operands lie in that one component. -/
theorem component_nonassociative :
    parentMeet (parentMeet first first) second = middle ∧
    parentMeet first (parentMeet first second) = first ∧ middle ≠ first := by decide +kernel

/-- Restricting both operands to this component still permits an arbitrary-target cycle. -/
theorem component_cycle : parentMeet first second = middle ∧ parentMeet middle first = first ∧
    middle ≠ first := by decide +kernel

end MicroCFTA.EqualityFixedDegreeCounterexample
