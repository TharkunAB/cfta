import MicroCFTA.InternedConstructorTemplates

/-!
# Literal parts of a root value

Root unions expose their literal members and ordinary rows. A Mu value
remains one literal atom. These predicates do not unfold its body.
-/
namespace MicroCFTA.SourceCurrentLiteralRootParts
open InternedConstructorTemplates

/-- A reference or Mu value reached through root unions only. -/
inductive Literal : Value Symbol Guard → Value Symbol Guard → Prop
  /-- A reference is one literal atom. -/
  | reference (name) : Literal (.reference name) (.reference name)
  /-- A complete Mu value is one literal atom. -/
  | mu (entry body depth ordinary) :
      Literal (.mu entry body depth ordinary) (.mu entry body depth ordinary)
  /-- A union retains the literal atoms of each member. -/
  | union {entry members level free value atom}
      (member : value ∈ members) (found : Literal value atom) :
      Literal (.union entry members level free) atom

/-- An ordinary row reached through root unions only. -/
inductive Row : Value Symbol Guard → EdgeValue Symbol Guard → Prop
  /-- An ordinary node exposes each stored row. -/
  | node {entry rows level free row} (member : row ∈ rows) :
      Row (.node entry rows level free) row
  /-- A union retains the ordinary rows of each member. -/
  | union {entry members level free value row}
      (member : value ∈ members) (found : Row value row) :
      Row (.union entry members level free) row

/-- A union exposes exactly the literal atoms of its members. -/
theorem literal_union (entry) (members : List (Value Symbol Guard)) (level free atom) :
    Literal (.union entry members level free) atom ↔
      ∃ value ∈ members, Literal value atom := by
  constructor
  · intro found
    cases found with
    | union member part => exact ⟨_, member, part⟩
  · rintro ⟨value, member, part⟩
    exact .union member part

/-- A union exposes exactly the ordinary rows of its members. -/
theorem row_union (entry) (members : List (Value Symbol Guard)) (level free row) :
    Row (.union entry members level free) row ↔
      ∃ value ∈ members, Row value row := by
  constructor
  · intro found
    cases found with
    | union member part => exact ⟨_, member, part⟩
  · rintro ⟨value, member, part⟩
    exact .union member part

/-- An ordinary node exposes exactly its stored rows. -/
theorem row_node (entry) (rows : List (EdgeValue Symbol Guard)) (level free row) :
    Row (.node entry rows level free) row ↔ row ∈ rows := by
  constructor
  · intro found
    cases found with
    | node member => exact member
  · exact Row.node

/-- Two values contain the same literal atoms and exact ordinary rows. -/
def SameParts (first second : Value Symbol Guard) : Prop :=
  (∀ atom, Literal first atom ↔ Literal second atom) ∧
    ∀ row, Row first row ↔ Row second row

end MicroCFTA.SourceCurrentLiteralRootParts
