import MicroCFTA.GeneratorCombinators

/-!
# Private support terms and user projection

The functions follow `Gen.Internal.Support` and `Gen.Label.surface`.
Private labels remain distinct from user labels. A projected term can be a
forest. Projection need not preserve rank identity.
-/
namespace MicroCFTA.SupportTerms
open Language GeneratorCombinators

mutual
/-- Retain user constructors and flatten every private constructor. -/
def surface : Term (Label Symbol) → List (Term Symbol)
  | .node (.user symbol) children => [.node symbol (surfaceForest children)]
  | .node _ children => surfaceForest children

/-- Project every child in order, including empty and multiple-root forests. -/
def surfaceForest : List (Term (Label Symbol)) → List (Term Symbol)
  | [] => []
  | first :: rest => surface first ++ surfaceForest rest
end

mutual
/-- Recognize exactly one binary private application step. -/
def applicationTermChildren : Term (Label Symbol) → Option (List (Term (Label Symbol)))
  | .node .apply [functions, argument] => some (applicationLeftChildren functions ++ [argument])
  | _ => none
termination_by term => sizeOf term

/-- Flatten a left application spine while retaining all argument terms. -/
def applicationLeftChildren : Term (Label Symbol) → List (Term (Label Symbol))
  | .node .pure [] => []
  | term => (applicationTermChildren term).getD [term]
termination_by term => sizeOf term + 1
end

/-- Close a layer with the source's special private-label cases. -/
def labelTerm (symbol : Symbol) (term : Term (Label Symbol)) : Term (Label Symbol) :=
  match term with
  | .node .joinN children => .node (.user symbol) children
  | .node (.choice _) [child] => labelTerm symbol child
  | .node .pure _ => .node (.user symbol) []
  | _ => .node (.user symbol) ((applicationTermChildren term).getD [term])

/-- Private pure nodes created by the library are always nullary. -/
def WellFormed : Term (Label Symbol) → Prop
  | .node label children => (label = .pure → children = []) ∧ ∀ child ∈ children, WellFormed child

/-- Forest projection preserves concatenation and its order. -/
theorem surface_append (left right : List (Term (Label Symbol))) :
    surfaceForest (left ++ right) = surfaceForest left ++ surfaceForest right := by
  induction left with
  | nil => rfl
  | cons first rest ih => simp [surfaceForest, ih, List.append_assoc]

/-- Flattening the left application spine preserves its complete user forest. -/
theorem applicationLeft_surface (term : Term (Label Symbol)) :
    surfaceForest (applicationLeftChildren term) = surface term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms,
      surfaceForest (applicationLeftChildren term) = surface term) with
  | node label children ih =>
    cases label <;> cases children with
    | nil => simp [applicationLeftChildren, applicationTermChildren, surface, surfaceForest]
    | cons first rest => cases rest with
      | nil => simp [applicationLeftChildren, applicationTermChildren, surface, surfaceForest]
      | cons second rest => cases rest with
        | nil =>
          simp [applicationLeftChildren, applicationTermChildren, surface, surfaceForest,
            surface_append, ih first (by simp)]
        | cons third rest => simp [applicationLeftChildren, applicationTermChildren, surface, surfaceForest]
  | nil => simp_all
  | cons first rest hf hr =>
    rename_i term member
    rcases List.mem_cons.mp member with rfl | member
    · exact hf
    · exact hr term member

/-- Successful spine recognition preserves the same user forest. -/
theorem application_surface (term : Term (Label Symbol)) (children : List (Term (Label Symbol)))
    (found : applicationTermChildren term = some children) : surfaceForest children = surface term := by
  cases term with
  | node label args =>
    cases label <;> cases args with
    | nil => simp [applicationTermChildren] at found
    | cons first rest => cases rest with
      | nil => simp [applicationTermChildren] at found
      | cons second rest => cases rest with
        | nil =>
          simp [applicationTermChildren] at found <;> subst children <;>
            simp [surface_append, applicationLeft_surface, surface, surfaceForest]
        | cons third rest => simp [applicationTermChildren] at found

/-- Labelling preserves every user child and inserts exactly one user root. -/
theorem label_surface (symbol : Symbol) (term : Term (Label Symbol)) (valid : WellFormed term) :
    surface (labelTerm symbol term) = [.node symbol (surface term)] := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, WellFormed term →
      surface (labelTerm symbol term) = [.node symbol (surface term)]) with
  | node label children ih =>
    simp only [WellFormed] at valid
    have childValid := valid.2
    cases label with
    | pure =>
      have empty := valid.1 rfl
      subst children
      rfl
    | choice branch =>
      cases children with
      | nil => simp [labelTerm, applicationTermChildren, surface, surfaceForest]
      | cons first rest => cases rest with
        | nil => simpa [labelTerm, surface, surfaceForest] using ih first (by simp) (childValid first (by simp))
        | cons second rest => simp [labelTerm, applicationTermChildren, surface, surfaceForest]
    | joinN => simp [labelTerm, surface]
    | apply =>
      cases children with
      | nil => simp [labelTerm, applicationTermChildren, surface, surfaceForest]
      | cons first rest => cases rest with
        | nil => simp [labelTerm, applicationTermChildren, surface, surfaceForest]
        | cons second rest => cases rest with
          | nil => simp [labelTerm, applicationTermChildren, surface, surfaceForest,
              surface_append, applicationLeft_surface]
          | cons third rest => simp [labelTerm, applicationTermChildren, surface, surfaceForest]
    | _ => simp [labelTerm, applicationTermChildren, surface, surfaceForest]
  | nil => simp_all
  | cons first rest hf hr =>
    rename_i term member valid
    rcases List.mem_cons.mp member with rfl | member
    · exact hf valid
    · exact hr term member valid

/-- A source pure member satisfies the private-node shape invariant. -/
theorem pure_valid : WellFormed (.node (.pure : Label Symbol) []) := by
  simp [WellFormed]

/-- Application preserves the shape invariant of both operands. -/
theorem apply_valid (left right : Term (Label Symbol)) (hl : WellFormed left) (hr : WellFormed right) :
    WellFormed (.node .apply [left, right]) := by simp [WellFormed, hl, hr]

/-- A choice wrapper preserves its child's shape invariant. -/
theorem choice_valid (index : Nat) (term : Term (Label Symbol)) (valid : WellFormed term) :
    WellFormed (.node (.choice index) [term]) := by simp [WellFormed, valid]

/-- Closing a member pays one size unit and preserves its decoded value. -/
def labelMember (symbol : Symbol) (member : Member Symbol Value) : Member Symbol Value :=
  {member with term := labelTerm symbol member.term, size := member.size + 1}

/-- Closing a finite source changes no probability or member position. -/
def labelMembers (symbol : Symbol) (members : Finite Symbol Value) : Finite Symbol Value :=
  Probability.map (labelMember symbol) members

/-- The label adapter preserves the complete decoded-value distribution. -/
theorem label_values (symbol : Symbol) (members : Finite Symbol Value) :
    values (labelMembers symbol members) = values members := by
  simp [values, labelMembers, labelMember, Probability.map, List.map_map]

/-- Every original replay position has the corresponding labelled outcome. -/
theorem label_select (symbol : Symbol) (members : Finite Symbol Value) (rank : Nat) :
    select (labelMembers symbol members) rank =
      (select members rank).map (fun (mass, member) => (mass, labelMember symbol member)) := by
  simp [select, labelMembers, Probability.map, List.getElem?_map]

/-- Projection deliberately identifies terms whose only difference is a private wrapper. -/
theorem surface_not_injective (symbol : Symbol) :
    let term : Term (Label Symbol) := .node (.user symbol) []
    term ≠ .node (.choice 0) [term] ∧ surface term = surface (.node (.choice 0) [term]) := by
  simp [surface, surfaceForest]

end MicroCFTA.SupportTerms
