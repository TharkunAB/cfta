import Std

/-!
# A nested cycle with equal Cartesian-closed images

Guard masks encode four distinct residual atoms. Bitwise union is their
canonical conjunction. Leaves retain finite alternative sets and the source
whole-node self shortcut. Unary parents retain the same shortcut.
The public Haskell witness uses four different guards that are all true.
This is an arbitrary-operand cycle, not a fixed equality-schedule cycle.
-/
namespace MicroCFTA.EqualityFixedSaturationCounterexample

/-- Insert one alternative in a finite sorted set. -/
def insert [Ord α] [BEq α] (value : α) : List α → List α
  | [] => [value]
  | first :: rest => if value == first then first :: rest else
      if compare value first == .lt then value :: first :: rest else first :: insert value rest

/-- Sort and deduplicate with structural recursion for kernel evaluation. -/
def canonical [Ord α] [BEq α] (values : List α) : List α := values.foldr insert []

/-- Expand every pair of leaf alternatives before the whole-node shortcut. -/
def leafProduct (first second : List Nat) : List Nat :=
  canonical (first.flatMap fun left => second.map (fun right => left ||| right))

/-- The source preserves an identical complete leaf instead of expanding its rows. -/
def leafMeet (first second : List Nat) : List Nat :=
  if first = second then first else leafProduct first second

/-- Unary parent Cartesian intersection applies source leaf intersection to child rows. -/
def parentProduct (first second : List (List Nat)) : List (List Nat) :=
  canonical (first.flatMap fun left => second.map (leafMeet left))

/-- The complete unary parent retains the same source identity shortcut. -/
def parentMeet (first second : List (List Nat)) : List (List Nat) :=
  if first = second then first else parentProduct first second

/-- Four original guard atoms. -/
def a : List Nat := [1, 2, 4, 8]

/-- Add the conjunction of the first two atoms while retaining all original alternatives. -/
def b : List Nat := [1, 2, 3, 4, 8]

/-- The first proper source leaf product has twelve alternatives. -/
def z : List Nat := leafMeet a b

/-- The second proper source leaf product contains all fifteen nonempty conjunctions. -/
def w : List Nat := leafMeet a z

/-- The first nested state retains both the original and the closed leaf. -/
def p : List (List Nat) := canonical [a, w]

/-- The expanding operand contains the original and the partly closed leaf. -/
def r : List (List Nat) := canonical [a, b]

/-- The second operand retains only the original leaf. -/
def q : List (List Nat) := [a]

/-- The first source parent product inserts the intermediate leaf. -/
def t : List (List Nat) := parentMeet p r

/-- Execute a finite number of full Cartesian self-product rounds. -/
def close : Nat → List Nat → List Nat
  | 0, rows => rows
  | rounds + 1, rows => close rounds (leafProduct rows rows)

/-- Four rounds suffice for the concrete four-atom witness below. -/
def leafClosure (rows : List Nat) : List Nat := close 4 rows

/-- Read recursively closed child rows before the parent Cartesian closure. -/
def childImages (rows : List (List Nat)) : List (List Nat) := canonical (rows.map leafClosure)

/-- The exact finite alternatives of both intermediate leaf products. -/
theorem leaf_rows : z = [1,2,3,4,5,6,7,8,9,10,11,12] ∧ w = List.range' 1 15 := by decide +kernel

/-- Both changing source-style intersections restore the earlier complete parent representation. -/
theorem alternating_cycle : t ≠ p ∧ parentMeet t q = p := by decide +kernel

/-- All operands have the same recursive child image, which is already Cartesian closed. -/
theorem same_closed_image : childImages p = [w] ∧ childImages r = [w] ∧ childImages q = [w] ∧
    childImages t = [w] ∧ leafProduct w w = w ∧ parentProduct [w] [w] = [w] := by decide +kernel

/-- No strict arbitrary-target rank exists even inside this one closed-image class. -/
theorem no_fiber_rank : ¬ ∃ rank : List (List Nat) → Nat,
    ∀ before target, childImages before = [w] → childImages target = [w] →
      parentMeet before target ≠ before → rank (parentMeet before target) < rank before := by
  rintro ⟨rank, decreasing⟩
  have first := decreasing p r same_closed_image.1 same_closed_image.2.1 alternating_cycle.1
  have back : parentMeet t q ≠ t := by rw [alternating_cycle.2]; exact Ne.symm alternating_cycle.1
  have second := decreasing t q same_closed_image.2.2.2.1 same_closed_image.2.2.1 back
  change rank t < rank p at first
  rw [alternating_cycle.2] at second
  omega

end MicroCFTA.EqualityFixedSaturationCounterexample
