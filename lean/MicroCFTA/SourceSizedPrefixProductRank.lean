import MicroCFTA.SourceSizedCandidates
import MicroCFTA.SourceSizedDecided

/-!
# Rank of original size-product rows

Natural budgets follow the source allocation order and current minimum table.
The source Integer conversion and reachable table construction remain separate.
The full row constraint is retained. The current equalSizes filter is a parameter.
-/
namespace MicroCFTA.SourceSizedPrefixProductRank
open SourceSizedDecided
variable {State Symbol Constraint : Type}

/-- Allocate the total to the original child states in their original order. -/
def allocations (minimum : State → Option Nat) :
    List State → Nat → List (List (State × Nat))
  | [], total => if total = 0 then [[]] else []
  | current :: rest, total =>
      match minimum current, rest.mapM minimum with
      | some smallest, some others =>
          (List.range (total + 1)).flatMap fun first =>
            if smallest ≤ first ∧ first + others.sum ≤ total then
              (allocations minimum rest (total - first)).map fun tail => (current, first) :: tail
            else []
      | _, _ => []

/-- Generated allocations retain child order, consume the total, and stay within it. -/
theorem allocations_spec (minimum : State → Option Nat) (states : List State)
    (total : Nat) (allocation : List (State × Nat))
    (member : allocation ∈ allocations minimum states total) :
    allocation.map Prod.fst = states ∧ (allocation.map Prod.snd).sum = total ∧
      ∀ entry ∈ allocation, entry.2 ≤ total := by
  induction states generalizing total allocation with
  | nil =>
      by_cases zero : total = 0
      · simp only [allocations, ite_eq_left zero, List.mem_singleton] at member
        subst allocation
        subst total
        simp
      · simp only [allocations, ite_eq_right zero, List.not_mem_nil] at member
  | cons current rest ih =>
      cases currentMinimum : minimum current with
      | none => simp only [allocations, currentMinimum, List.not_mem_nil] at member
      | some smallest =>
        cases restMinimum : rest.mapM minimum with
        | none => simp only [allocations, currentMinimum, restMinimum, List.not_mem_nil] at member
        | some others =>
          simp only [allocations, currentMinimum, restMinimum, List.mem_flatMap] at member
          obtain ⟨first, firstRange, found⟩ := member
          by_cases permitted : smallest ≤ first ∧ first + others.sum ≤ total
          · simp only [ite_eq_left permitted, List.mem_map] at found
            obtain ⟨tail, tailMember, same⟩ := found
            subst allocation
            obtain ⟨order, consumed, bounds⟩ := ih (total - first) tail tailMember
            have firstBound := (SourceSizedCandidates.child_size_lt firstRange).1
            refine ⟨?_, ?_, ?_⟩
            · simpa only [List.map_cons] using congrArg (List.cons current) order
            · simp only [List.map_cons, List.sum_cons]
              rw [consumed]
              omega
            · intro entry listed
              rcases List.mem_cons.mp listed with rfl | inTail
              · omega
              · exact Nat.le_trans (bounds entry inTail) (Nat.sub_le _ _)
          · simp only [ite_eq_right permitted, List.not_mem_nil] at found

/-- Copy an original row and replace only its children by their allocated pairs. -/
def allocatedRow (original : Row State Symbol Constraint) (allocation : List (State × Nat)) :
    Row (Option (State × Nat)) Symbol Constraint :=
  ⟨original.label, allocation.map some, original.constraint⟩

/-- Generate one positive-size row class with the current numeric constraint filter. -/
def rowOf (original : State → List (Row State Symbol Constraint))
    (minimum : State → Option Nat) (equalSizes : Constraint → List Nat → Bool)
    (state : State) : Nat → List (Row (Option (State × Nat)) Symbol Constraint)
  | 0 => []
  | total + 1 =>
      (original state).flatMap fun row =>
        ((allocations minimum row.children total).filter fun allocation =>
          equalSizes row.constraint (allocation.map Prod.snd)).map (allocatedRow row)

/-- Every generated row retains its original fields and strictly smaller child budgets. -/
theorem rowOf_origin (original : State → List (Row State Symbol Constraint))
    (minimum : State → Option Nat) (equalSizes : Constraint → List Nat → Bool)
    (state : State) (parent : Nat) (row : Row (Option (State × Nat)) Symbol Constraint)
    (member : row ∈ rowOf original minimum equalSizes state parent) :
    ∃ source ∈ original state, ∃ allocation : List (State × Nat),
      equalSizes source.constraint (allocation.map Prod.snd) = true ∧
      row.label = source.label ∧ row.constraint = source.constraint ∧
      row.children = allocation.map some ∧ allocation.map Prod.fst = source.children ∧
      ∀ entry ∈ allocation, entry.2 < parent := by
  cases parent with
  | zero => simp only [rowOf, List.not_mem_nil] at member
  | succ total =>
      simp only [rowOf, List.mem_flatMap] at member
      obtain ⟨source, sourceMember, found⟩ := member
      obtain ⟨allocation, kept, same⟩ := List.mem_map.mp found
      obtain ⟨allocated, checked⟩ := List.mem_filter.mp kept
      obtain ⟨order, _consumed, bounds⟩ := allocations_spec minimum source.children total allocation allocated
      subst row
      exact ⟨source, sourceMember, allocation, checked, rfl, rfl, rfl, order,
        fun entry listed => Nat.lt_succ_of_le (bounds entry listed)⟩

/-- The synthetic root has a rank above every original requested root budget. -/
def rank (bound : Int) : Option (State × Nat) → Nat
  | none => bound.toNat + 1
  | some (_, budget) => budget

/-- Generate the synthetic root directly from positive root sizes without an extra node. -/
def rows (original : State → List (Row State Symbol Constraint))
    (minimum : State → Option Nat) (equalSizes : Constraint → List Nat → Bool)
    (root : State) (bound : Int) : Option (State × Nat) → List (Row (Option (State × Nat)) Symbol Constraint)
  | none => (List.range bound.toNat).flatMap fun offset => rowOf original minimum equalSizes root (offset + 1)
  | some (state, budget) => rowOf original minimum equalSizes state budget

private theorem rowOf_child_rank (original : State → List (Row State Symbol Constraint))
    (minimum : State → Option Nat) (equalSizes : Constraint → List Nat → Bool)
    (bound : Int) (state : State) (parent : Nat)
    (row : Row (Option (State × Nat)) Symbol Constraint)
    (member : row ∈ rowOf original minimum equalSizes state parent)
    (child : Option (State × Nat)) (listed : child ∈ row.children) : rank bound child < parent := by
  obtain ⟨source, _sourceMember, allocation, _checked, _label, _constraint, children, _order, bounds⟩ :=
    rowOf_origin original minimum equalSizes state parent row member
  rw [children] at listed
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp listed
  subst child
  exact bounds entry entryMember

/-- Every generated edge strictly lowers the explicit original size-product rank. -/
theorem rows_rank (original : State → List (Row State Symbol Constraint))
    (minimum : State → Option Nat) (equalSizes : Constraint → List Nat → Bool)
    (root : State) (bound : Int) (parent : Option (State × Nat))
    (row : Row (Option (State × Nat)) Symbol Constraint) (member : row ∈ rows original minimum equalSizes root bound parent)
    (child : Option (State × Nat)) (listed : child ∈ row.children) : rank bound child < rank bound parent := by
  cases parent with
  | none =>
      simp only [rows, List.mem_flatMap] at member
      obtain ⟨offset, offsetRange, selected⟩ := member
      have smaller := rowOf_child_rank original minimum equalSizes bound root (offset + 1) row selected child listed
      have within := List.mem_range.mp offsetRange
      change rank bound child < bound.toNat + 1
      omega
  | some pair =>
      rcases pair with ⟨state, budget⟩
      exact rowOf_child_rank original minimum equalSizes bound state budget row member child listed

/-- A nonpositive original size bound generates no synthetic-root row. -/
theorem root_nonpositive (original : State → List (Row State Symbol Constraint))
    (minimum : State → Option Nat) (equalSizes : Constraint → List Nat → Bool)
    (root : State) (bound : Int) (nonpositive : bound ≤ 0) :
    rows original minimum equalSizes root bound none = [] := by
  have zero : bound.toNat = 0 := by omega
  simp [rows, zero]

end MicroCFTA.SourceSizedPrefixProductRank
