import MicroCFTA.SourceSizedDecided

/-!
# Same-token tuples of conjunction transitions

The source reads a conjunction key in its set order. It chooses a row
from the first owner. It then reads the list product of the later owners'
rows, filtered by the first row's symbol and arity. No duplicate is removed.
An empty key emits no tuple.

This module specifies that tuple list before transition intersection and
the per-key transition cap. It does not define the conjunction worklist or
prove native storage and execution resource bounds.
-/
namespace MicroCFTA.SourceSizedConjunctionTuples
open Language SourceSizedDecided

/-- Compare the complete source token, including both symbol and child arity. -/
def sameToken [DecidableEq Symbol]
    (first second : Row State Symbol (List (List Nat))) : Bool :=
  decide (first.label = second.label) && decide (first.children.length = second.children.length)

/-- A source token matches exactly when both its symbol and arity match. -/
theorem sameToken_iff [DecidableEq Symbol]
    (first second : Row State Symbol (List (List Nat))) :
    sameToken first second = true ↔
      first.label = second.label ∧ first.children.length = second.children.length := by
  simp only [sameToken, Bool.and_eq_true, decide_eq_true_eq]

/-- Enumerate the literal first-row and filtered later-row products in source order. -/
def tuples [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat)))) :
    List State → List (List (Row State Symbol (List (List Nat))))
  | [] => []
  | state :: states =>
      (lookup state).flatMap fun first =>
        (products (fun owner => (lookup owner).filter (sameToken first)) states).map (first :: ·)

/-- The source empty-key case emits no transition tuple. -/
theorem empty_key [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat)))) : tuples lookup [] = [] := rfl

private theorem mem_filtered_products [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (first : Row State Symbol (List (List Nat))) (states : List State)
    (tail : List (Row State Symbol (List (List Nat)))) :
    tail ∈ products (fun owner => (lookup owner).filter (sameToken first)) states ↔
      All₂ (fun owner row => row ∈ lookup owner ∧ sameToken first row = true) states tail := by
  simp only [mem_products, List.mem_filter]

/-- Nonempty-key tuples are exactly one first row and pointwise filtered later rows. -/
theorem mem_tuples_cons [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (state : State) (states : List State) (tuple : List (Row State Symbol (List (List Nat)))) :
    tuple ∈ tuples lookup (state :: states) ↔
      ∃ first ∈ lookup state, ∃ tail, tuple = first :: tail ∧
        All₂ (fun owner row => row ∈ lookup owner ∧ sameToken first row = true) states tail := by
  constructor
  · intro member
    obtain ⟨first, stored, mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨tail, selected, rfl⟩ := List.mem_map.mp mapped
    exact ⟨first, stored, tail, rfl, (mem_filtered_products lookup first states tail).mp selected⟩
  · rintro ⟨first, stored, tail, rfl, related⟩
    exact List.mem_flatMap.mpr ⟨first, stored, List.mem_map.mpr
      ⟨tail, (mem_filtered_products lookup first states tail).mpr related, rfl⟩⟩

/-- Every emitted tuple has one original row at each corresponding key position. -/
theorem tuple_origin [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (tuple : List (Row State Symbol (List (List Nat))))
    (member : tuple ∈ tuples lookup key) :
    All₂ (fun owner row => row ∈ lookup owner) key tuple := by
  cases key with
  | nil => cases member
  | cons state states =>
      obtain ⟨first, stored, tail, rfl, related⟩ := (mem_tuples_cons lookup state states tuple).mp member
      exact .cons stored (related.imp (fun _ _ facts => facts.1))

/-- Every emitted tuple has exactly as many transitions as the key has owners. -/
theorem tuple_length [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (tuple : List (Row State Symbol (List (List Nat))))
    (member : tuple ∈ tuples lookup key) : tuple.length = key.length :=
  (tuple_origin lookup key tuple member).length_eq.symm

/-- Every emitted tuple contains its selected first transition. -/
theorem tuple_nonempty [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (tuple : List (Row State Symbol (List (List Nat))))
    (member : tuple ∈ tuples lookup key) : tuple ≠ [] := by
  cases key with
  | nil => cases member
  | cons state states =>
      obtain ⟨first, _, tail, rfl, _⟩ := (mem_tuples_cons lookup state states tuple).mp member
      exact List.cons_ne_nil _ _

private theorem related_member_right {A B : Type} {relation : A → B → Prop}
    {first : List A} {second : List B} (related : All₂ relation first second)
    (value : B) (member : value ∈ second) : ∃ owner ∈ first, relation owner value := by
  induction related with
  | nil => cases member
  | @cons owner head owners tail found rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨owner, by simp, found⟩
      · obtain ⟨source, present, related⟩ := ih later
        exact ⟨source, List.mem_cons_of_mem owner present, related⟩

/-- Every selected row comes from an owner in the conjunction key. -/
theorem row_origin [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (tuple : List (Row State Symbol (List (List Nat))))
    (member : tuple ∈ tuples lookup key) (row : Row State Symbol (List (List Nat)))
    (selected : row ∈ tuple) : ∃ owner ∈ key, row ∈ lookup owner :=
  related_member_right (tuple_origin lookup key tuple member) row selected

/-- All selected transitions have the same complete symbol-and-arity token. -/
theorem common_token [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (tuple : List (Row State Symbol (List (List Nat))))
    (member : tuple ∈ tuples lookup key)
    (left right : Row State Symbol (List (List Nat))) (leftIn : left ∈ tuple) (rightIn : right ∈ tuple) :
    sameToken left right = true := by
  cases key with
  | nil => cases member
  | cons state states =>
      obtain ⟨first, _, tail, rfl, related⟩ := (mem_tuples_cons lookup state states tuple).mp member
      have allMembers : ∀ row ∈ first :: tail,
          first.label = row.label ∧ first.children.length = row.children.length := by
        intro row selected
        rcases List.mem_cons.mp selected with rfl | later
        · exact ⟨rfl, rfl⟩
        · obtain ⟨_, _, facts⟩ := related_member_right related row later
          exact (sameToken_iff first row).mp facts.2
      have leftToken := allMembers left leftIn
      have rightToken := allMembers right rightIn
      exact (sameToken_iff left right).mpr
        ⟨leftToken.1.symm.trans rightToken.1, leftToken.2.symm.trans rightToken.2⟩

/-- The common token gives a common symbol and a common number of children. -/
theorem common_shape [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (tuple : List (Row State Symbol (List (List Nat))))
    (member : tuple ∈ tuples lookup key)
    (left right : Row State Symbol (List (List Nat))) (leftIn : left ∈ tuple) (rightIn : right ∈ tuple) :
    left.label = right.label ∧ left.children.length = right.children.length :=
  (sameToken_iff left right).mp (common_token lookup key tuple member left right leftIn rightIn)

end MicroCFTA.SourceSizedConjunctionTuples
