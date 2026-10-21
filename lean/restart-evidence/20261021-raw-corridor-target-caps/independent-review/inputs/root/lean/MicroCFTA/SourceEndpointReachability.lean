import MicroCFTA.InternedConstructorTemplates

/-!
# The endpoint descendant check from main 24a710a3

The source checks cached depth before each node tag. It stops at a Mu and
reads its constraint predicate. It traverses ordinary children and stored
union members. It does not unfold a Mu or read either construction probe.
The global Haskell memo and its storage remain separate source boundaries.
-/
namespace MicroCFTA.SourceEndpointReachability
open InternedConstructorTemplates

mutual
/-- Execute the source endpoint descendant check on complete stored records. -/
def reaches (unconstrained : Value Symbol Guard → Bool) (value : Value Symbol Guard) : Bool :=
  if value.depth == 0 then false else
    match value with
    | .mu .. => !unconstrained value
    | .union _ members _ _ => many unconstrained members
    | .node _ edges _ _ => rows unconstrained edges
    | _ => false
termination_by sizeOf value

/-- Check stored members in source order and stop at the first true result. -/
def many (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard)) : Bool :=
  match values with
  | [] => false
  | first :: rest => reaches unconstrained first || many unconstrained rest
termination_by sizeOf values

/-- Traverse the original edge children without inspecting edge annotations. -/
def rows (unconstrained : Value Symbol Guard → Bool) (edges : List (EdgeValue Symbol Guard)) : Bool :=
  match edges with
  | [] => false
  | .mk _ children :: rest => many unconstrained children || rows unconstrained rest
termination_by sizeOf edges
end

/-- A witness follows only source branches whose cached depth permits traversal. -/
inductive Witness (unconstrained : Value Symbol Guard → Bool) : Value Symbol Guard → Prop where
  | binder (constrained : unconstrained (.mu entry body depth ordinary) = false) :
      Witness unconstrained (.mu entry body depth ordinary)
  | union (nested : depth ≠ 0) (member : child ∈ members) (next : Witness unconstrained child) :
      Witness unconstrained (.union entry members depth free)
  | node (nested : depth ≠ 0) (edge : row ∈ edges) (member : child ∈ row.children)
      (next : Witness unconstrained child) : Witness unconstrained (.node entry edges depth free)

mutual
/-- The computed Boolean has exactly a constrained-Mu witness through the source traversal. -/
theorem reaches_iff (unconstrained : Value Symbol Guard → Bool) (value : Value Symbol Guard) :
    reaches unconstrained value = true ↔ Witness unconstrained value := by
  cases value with
  | empty => simp [reaches, Value.depth]; intro impossible; cases impossible
  | reference name => simp [reaches, Value.depth]; intro impossible; cases impossible
  | mu entry body depth ordinary =>
      simp only [reaches, Value.depth, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        beq_iff_eq, ↓reduceIte, Bool.not_eq_true']
      constructor
      · exact Witness.binder
      · intro found; cases found; assumption
  | union entry members depth free =>
      by_cases zero : depth = 0
      · simp only [reaches, Value.depth, zero, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
          false_iff]
        intro found; cases found with | union nested _ _ => exact nested rfl
      · rw [reaches]
        simp only [Value.depth, beq_iff_eq, zero, ↓reduceIte]
        rw [many_iff unconstrained members]
        constructor
        · rintro ⟨child, member, found⟩; exact Witness.union zero member found
        · intro found; cases found with | union _ member next => exact ⟨_, member, next⟩
  | node entry edges depth free =>
      by_cases zero : depth = 0
      · simp only [reaches, Value.depth, zero, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
          false_iff]
        intro found; cases found with | node nested _ _ _ => exact nested rfl
      · rw [reaches]
        simp only [Value.depth, beq_iff_eq, zero, ↓reduceIte]
        rw [rows_iff unconstrained edges]
        constructor
        · rintro ⟨row, member, child, selected, found⟩; exact Witness.node zero member selected found
        · intro found; cases found with | node _ member selected next => exact ⟨_, member, _, selected, next⟩
termination_by sizeOf value

/-- A member scan succeeds exactly when one original member has a witness. -/
theorem many_iff (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard)) :
    many unconstrained values = true ↔ ∃ value ∈ values, Witness unconstrained value := by
  cases values with
  | nil => simp [many]
  | cons first rest => simp [many, reaches_iff unconstrained first, many_iff unconstrained rest]
termination_by sizeOf values

/-- An edge scan succeeds exactly when an original child has a witness. -/
theorem rows_iff (unconstrained : Value Symbol Guard → Bool) (edges : List (EdgeValue Symbol Guard)) :
    rows unconstrained edges = true ↔ ∃ edge ∈ edges, ∃ child ∈ edge.children, Witness unconstrained child := by
  cases edges with
  | nil => simp [rows]
  | cons first rest => cases first with
    | mk entry children => simp [rows, many_iff unconstrained children, rows_iff unconstrained rest, EdgeValue.children]
termination_by sizeOf edges
end

/-- Zero cached depth stops the traversal before the node tag is inspected. -/
theorem zero_clear (unconstrained : Value Symbol Guard → Bool) (value : Value Symbol Guard)
    (zero : value.depth = 0) : reaches unconstrained value = false := by
  cases value <;> simp_all [reaches, Value.depth]

/-- A Mu reads its predicate and does not traverse its stored body or probes. -/
theorem binder (unconstrained : Value Symbol Guard → Bool) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) :
    reaches unconstrained (.mu entry body depth ordinary) = !unconstrained (.mu entry body depth ordinary) := by
  simp [reaches, Value.depth]

end MicroCFTA.SourceEndpointReachability
