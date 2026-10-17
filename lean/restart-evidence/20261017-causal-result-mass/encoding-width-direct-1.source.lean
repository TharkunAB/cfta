import MicroCFTA.InternedValueMass
import MicroCFTA.InternedStoredSubstitution

/-!
# Literal constructor widths from stored input mass

The full stored encoder retains bounded row, member, and child list lengths.
The bound uses the initial complete value mass. It covers nested Mu and
unions, arbitrary lexical contexts, and the closed-value shortcut.
-/
namespace MicroCFTA.InternedStoredEncodingWidth
open InternedConstructorTemplates InternedStoredSubstitution
open InternedNestedConstruction (Syntax EdgeSyntax)
local notation "M" => InternedValueMass
variable {Symbol Guard : Type}

mutual
/-- Bound every literal list consumed by one constructor expression. -/
def Width (bound : Nat) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node rows => rows.length ≤ bound ∧ Rows bound rows
  | .union members => members.length ≤ bound ∧ Many bound members
  | .binder _ body => Width bound body
termination_by expression => sizeOf expression

/-- Every ordered member retains the same initial width bound. -/
def Many (bound : Nat) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Width bound first ∧ Many bound rest
termination_by expressions => sizeOf expressions

/-- Raw rows bound their child lists and all nested child expressions. -/
def Rows (bound : Nat) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => children.length ≤ bound ∧ Many bound children ∧ Rows bound rest
termination_by expressions => sizeOf expressions
end

mutual
/-- Increasing the initial bound retains every constructor width. -/
theorem width_mono (first last : Nat) (bounded : first ≤ last) (expression : Syntax Symbol Guard)
    (known : Width first expression) : Width last expression := by
  cases expression with
  | empty | var => trivial
  | node rows => exact ⟨Nat.le_trans known.1 bounded, rows_mono first last bounded rows known.2⟩
  | union members => exact ⟨Nat.le_trans known.1 bounded, many_mono first last bounded members known.2⟩
  | binder _ body => exact width_mono first last bounded body known
termination_by sizeOf expression

/-- Increasing the initial bound retains all ordered members. -/
theorem many_mono (first last : Nat) (bounded : first ≤ last) (expressions : List (Syntax Symbol Guard))
    (known : Many first expressions) : Many last expressions := by
  cases expressions with
  | nil => trivial
  | cons head tail => exact ⟨width_mono first last bounded head known.1, many_mono first last bounded tail known.2⟩
termination_by sizeOf expressions

/-- Increasing the initial bound retains all raw rows and child lists. -/
theorem rows_mono (first last : Nat) (bounded : first ≤ last) (expressions : List (EdgeSyntax Symbol Guard))
    (known : Rows first expressions) : Rows last expressions := by
  cases expressions with
  | nil => trivial
  | cons head tail =>
      cases head with
      | mk _ _ children =>
          exact ⟨Nat.le_trans known.1 bounded, many_mono first last bounded children known.2.1,
            rows_mono first last bounded tail known.2.2⟩
termination_by sizeOf expressions
end

/-- Complete value-list mass bounds its literal length. -/
theorem values_length (members : List (Value Symbol Guard)) : members.length ≤ M.values members := by
  rw [M.values_eq_length_sum]
  omega

/-- Complete edge-list mass bounds its literal length. -/
theorem edges_length (rows : List (EdgeValue Symbol Guard)) : rows.length ≤ M.edges rows := by
  rw [M.edges_eq_length_sum]
  omega

mutual
/-- The initial complete value mass bounds every list in its full stored encoding. -/
theorem encode_width (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (value : Value Symbol Guard) (bound : Nat) (small : M.value value ≤ bound) :
    Width bound (encode context locals value) := by
  rw [encode.eq_def]
  split
  · trivial
  · cases value with
    | empty => trivial
    | reference name =>
        cases locals.findIdx? (· == name) <;> trivial
    | node entry rows depth free =>
        have measured : M.edges rows ≤ bound := by simp only [M.value] at small; omega
        exact ⟨by simpa only [encodeEdges_length] using Nat.le_trans (edges_length rows) measured,
          encodeEdges_width context locals rows bound measured⟩
    | union entry members depth free =>
        have measured : M.values members ≤ bound := by simp only [M.value] at small; omega
        exact ⟨by simpa only [encodeMany_length] using Nat.le_trans (values_length members) measured,
          encodeMany_width context locals members bound measured⟩
    | mu entry body depth ordinary =>
        apply encode_width context (.interned entry.identity :: locals) body bound
        simp only [M.value] at small
        omega
termination_by sizeOf value

/-- The initial complete member-list mass bounds every encoded child expression. -/
theorem encodeMany_width (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (members : List (Value Symbol Guard)) (bound : Nat) (small : M.values members ≤ bound) :
    Many bound (encodeMany context locals members) := by
  cases members with
  | nil => trivial
  | cons first rest =>
      simp only [M.values] at small
      exact ⟨encode_width context locals first bound (by omega), encodeMany_width context locals rest bound (by omega)⟩
termination_by sizeOf members

/-- The initial complete row-list mass bounds every encoded child list and row. -/
theorem encodeEdges_width (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (rows : List (EdgeValue Symbol Guard)) (bound : Nat) (small : M.edges rows ≤ bound) :
    Rows bound (encodeEdges context locals rows) := by
  cases rows with
  | nil => trivial
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [M.edges, M.edge] at small
          exact ⟨by simpa only [encodeMany_length] using Nat.le_trans (values_length children) (show M.values children ≤ bound by omega),
            encodeMany_width context locals children bound (by omega), encodeEdges_width context locals rest bound (by omega)⟩
termination_by sizeOf rows
end

end MicroCFTA.InternedStoredEncodingWidth
