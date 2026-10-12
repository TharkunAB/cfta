import Std

/-!
# Structural comparison through finite ordered trees

Constructor tags precede fields. Field lists use lexicographic comparison.
Finite approximations prove the recursive comparison's order laws.
-/
namespace MicroCFTA.StructuralOrder

/-- A sum comparison puts every left value before every right value. -/
def sumCompare (left : α → α → Ordering) (right : β → β → Ordering) : Sum α β → Sum α β → Ordering
  | .inl a, .inl b => left a b
  | .inr a, .inr b => right a b
  | .inl _, .inr _ => .lt
  | .inr _, .inl _ => .gt

instance (left : α → α → Ordering) (right : β → β → Ordering)
    [Std.OrientedCmp left] [Std.OrientedCmp right] : Std.OrientedCmp (sumCompare left right) where
  eq_swap := by
    intro a b
    cases a <;> cases b <;> simp only [sumCompare]
    · exact Std.OrientedCmp.eq_swap
    · rfl
    · rfl
    · exact Std.OrientedCmp.eq_swap

instance (left : α → α → Ordering) (right : β → β → Ordering)
    [Std.TransCmp left] [Std.TransCmp right] : Std.TransCmp (sumCompare left right) where
  isLE_trans := by
    intro a b c ab bc
    cases a <;> cases b <;> cases c <;> simp only [sumCompare, Ordering.isLE] at ab bc ⊢
    all_goals try contradiction
    all_goals try rfl
    all_goals exact Std.TransCmp.isLE_trans ab bc

/-- Primitive ordered fields and recursively ordered constructor fields. -/
inductive Key where
  | nat (value : Nat)
  | int (value : Int)
  | text (value : String)
  | node (tag : Nat) (fields : List Key)
  deriving Repr

/-- A nonrecursive view permits reuse of the ordinary sum, product, and list order laws. -/
def view : Key → Sum Nat (Sum Int (Sum String (Nat × List Key)))
  | .nat value => .inl value
  | .int value => .inr (.inl value)
  | .text value => .inr (.inr (.inl value))
  | .node tag fields => .inr (.inr (.inr (tag, fields)))

/-- Compare one level, using the supplied comparison for child fields. -/
def step (nested : Key → Key → Ordering) (first second : Key) : Ordering :=
  letI : Ord Key := ⟨nested⟩
  letI : Ord (Nat × List Key) := lexOrd
  sumCompare compare (sumCompare compare (sumCompare compare compare)) (view first) (view second)

instance (nested : Key → Key → Ordering) [Std.TransCmp nested] : Std.TransCmp (step nested) where
  eq_swap := by
    letI : Ord Key := ⟨nested⟩
    letI : Ord (Nat × List Key) := lexOrd
    intro a b
    exact Std.OrientedCmp.eq_swap (cmp := sumCompare compare (sumCompare (compare (α := Int)) (sumCompare (compare (α := String)) (compare (α := Nat × List Key)))))
  isLE_trans := by
    letI : Ord Key := ⟨nested⟩
    letI : Ord (Nat × List Key) := lexOrd
    intro a b c ab bc
    exact Std.TransCmp.isLE_trans (cmp := sumCompare compare (sumCompare (compare (α := Int)) (sumCompare (compare (α := String)) (compare (α := Nat × List Key))))) ab bc

/-- Finite comparison reads no more than the supplied number of recursive field levels. -/
def compareFuel : Nat → Key → Key → Ordering
  | 0, _, _ => .eq
  | fuel + 1, first, second => step (compareFuel fuel) first second

instance fuelTrans (fuel : Nat) : Std.TransCmp (compareFuel fuel) := by
  induction fuel with
  | zero => exact { eq_swap := rfl, isLE_trans := fun _ _ => rfl }
  | succ fuel ih =>
      letI := ih
      exact inferInstanceAs (Std.TransCmp (step (compareFuel fuel)))

mutual
/-- Complete constructor comparison follows every field lexicographically. -/
def compareKey : Key → Key → Ordering
  | .nat a, .nat b => compare a b
  | .int a, .int b => compare a b
  | .text a, .text b => compare a b
  | .node a as, .node b bs => (compare a b).then (compareKeys as bs)
  | .nat _, _ => .lt
  | _, .nat _ => .gt
  | .int _, _ => .lt
  | _, .int _ => .gt
  | .text _, _ => .lt
  | _, .text _ => .gt
termination_by first _ => sizeOf first

/-- Field-list comparison keeps the source list order and repetitions. -/
def compareKeys : List Key → List Key → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compareKey a b).then (compareKeys as bs)
termination_by first _ => sizeOf first
end

theorem compareKeys_lex (first second : List Key) : compareKeys first second = List.compareLex compareKey first second := by
  induction first generalizing second with
  | nil => cases second <;> simp [compareKeys, List.compareLex]
  | cons head tail ih => cases second with
    | nil => simp only [compareKeys, List.compareLex_cons_nil]
    | cons b bs => rw [compareKeys, List.compareLex_cons_cons, ih]

private theorem lex_congr (first second : List Key) (left right : Key → Key → Ordering)
    (agree : ∀ a ∈ first, ∀ b, left a b = right a b) : List.compareLex left first second = List.compareLex right first second := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons head tail ih => cases second with
    | nil => rfl
    | cons b bs => rw [List.compareLex_cons_cons, List.compareLex_cons_cons, agree head (by simp) b,
        ih bs (fun a member => agree a (by simp [member]))]

/-- Enough finite levels give exactly the complete comparison, without bounding the right argument. -/
theorem fuel_exact (fuel : Nat) (first second : Key) (enough : sizeOf first < fuel) :
    compareFuel fuel first second = compareKey first second := by
  induction fuel generalizing first second with
  | zero => omega
  | succ fuel ih =>
      cases first <;> cases second <;> simp only [compareFuel, step, view, sumCompare, compareKey]
      rename_i tag fields otherTag otherFields
      change (compare tag otherTag).then (List.compareLex (compareFuel fuel) fields otherFields) =
        (compare tag otherTag).then (compareKeys fields otherFields)
      rw [compareKeys_lex]
      congr 1
      apply lex_congr
      intro child member other
      apply ih child other
      have smaller := List.sizeOf_lt_of_mem member
      simp only [Key.node.sizeOf_spec] at enough
      omega

/-- The complete recursive source-style comparison has transitive non-strict order. -/
instance keyTrans : Std.TransCmp compareKey where
  eq_swap := by
    intro first second
    let fuel := sizeOf first + sizeOf second + 1
    have swap := Std.OrientedCmp.eq_swap (cmp := compareFuel fuel) (a := first) (b := second)
    simpa only [fuel_exact fuel first second (by dsimp [fuel]; omega), fuel_exact fuel second first (by dsimp [fuel]; omega)] using swap
  isLE_trans := by
    intro first second third ab bc
    let fuel := sizeOf first + sizeOf second + sizeOf third + 1
    have firstEq := fuel_exact fuel first second (by dsimp [fuel]; omega)
    have secondEq := fuel_exact fuel second third (by dsimp [fuel]; omega)
    have resultEq := fuel_exact fuel first third (by dsimp [fuel]; omega)
    rw [← firstEq] at ab
    rw [← secondEq] at bc
    rw [← resultEq]
    exact Std.TransCmp.isLE_trans ab bc

end MicroCFTA.StructuralOrder
