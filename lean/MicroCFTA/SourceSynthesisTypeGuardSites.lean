import MicroCFTA.SourceSynthesisGeneralizeSyntax

/-!
# Literal row sites in original Type syntax

Addresses retain row, child, union-member, and binder-body positions.
Generalization changes only a singleton outer row. Replacement does not
traverse the inserted universe. These laws concern literal source syntax.
Physical warm winners and generated guard placement remain separate.
-/
namespace MicroCFTA.SourceSynthesisTypeGuardSites
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceSynthesisTypeSyntax (Ty Expr typeNode allTypes)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard generalize replace finish rootSymbol equalityClasses)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)
local notation "Row" => EdgeSyntax String Guard

/-- A source address distinguishes each actual structural position. -/
inductive Position where
  /-- A child position retains its containing row and ordered child index. -/
  | child (rowIndex childIndex : Nat)
  /-- A union position retains its ordered member index. -/
  | member (memberIndex : Nat)
  /-- A binder has one body position. -/
  | body

/-- A literal row occurrence retains its address and exact final row index. -/
inductive RowAt : Expr Guard → List Position → Nat → Row → Prop where
  /-- A root row has its actual indexed list lookup. -/
  | node {rows : List Row} {index : Nat} {row : Row}
      (selected : rows[index]? = some row) : RowAt (.node rows) [] index row
  /-- A child descent retains the containing row and child lookups. -/
  | child {rows : List Row} {symbol : String} {guard : Guard} {children : List (Expr Guard)}
      {value : Expr Guard} {address : List Position} {index : Nat} {row : Row}
      (rowIndex childIndex : Nat)
      (owner : rows[rowIndex]? = some (.mk symbol guard children))
      (selected : children[childIndex]? = some value) (rest : RowAt value address index row) :
      RowAt (.node rows) (.child rowIndex childIndex :: address) index row
  /-- A union descent retains its actual ordered member lookup. -/
  | member {values : List (Expr Guard)} {value : Expr Guard} {address : List Position} {index : Nat} {row : Row}
      (memberIndex : Nat) (selected : values[memberIndex]? = some value) (rest : RowAt value address index row) :
      RowAt (.union values) (.member memberIndex :: address) index row
  /-- A binder descent visits its literal body. -/
  | body {smart : Bool} {value : Expr Guard} {address : List Position} {index : Nat} {row : Row}
      (rest : RowAt value address index row) : RowAt (.binder smart value) (.body :: address) index row

private theorem children_guard_mem {values : List (Expr Guard)} {value : Expr Guard} {guard : Guard}
    (selected : value ∈ values) (present : guard ∈ guards value) : guard ∈ childGuards values := by
  induction values with
  | nil => cases selected
  | cons first rest ih =>
      rcases List.mem_cons.mp selected with rfl | selected
      · exact List.mem_append_left _ present
      · exact List.mem_append_right _ (ih selected)

private theorem row_guard_mem {rows : List Row} {symbol : String} {guard : Guard} {children : List (Expr Guard)}
    (selected : .mk symbol guard children ∈ rows) : guard ∈ edgeGuards rows := by
  induction rows with
  | nil => cases selected
  | cons first rest ih =>
      cases first with
      | mk name own values =>
          rcases List.mem_cons.mp selected with same | selected
          · cases same
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih selected))

private theorem row_child_guard_mem {rows : List Row} {symbol : String} {own guard : Guard}
    {children : List (Expr Guard)} (selected : .mk symbol own children ∈ rows)
    (present : guard ∈ childGuards children) : guard ∈ edgeGuards rows := by
  induction rows with
  | nil => cases selected
  | cons first rest ih =>
      cases first with
      | mk name field values =>
          rcases List.mem_cons.mp selected with same | selected
          · cases same
            exact List.mem_cons_of_mem _ (List.mem_append_left _ present)
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih selected))

/-- Every addressed row contributes its complete guard to the literal inventory. -/
theorem RowAt.guard_mem {expression : Expr Guard} {address : List Position} {index : Nat}
    {symbol : String} {guard : Guard} {children : List (Expr Guard)}
    (occurrence : RowAt expression address index (.mk symbol guard children)) : guard ∈ guards expression := by
  cases occurrence with
  | node selected => exact row_guard_mem (List.mem_of_getElem? selected)
  | child rowIndex childIndex owner selected rest =>
      exact row_child_guard_mem (List.mem_of_getElem? owner)
        (children_guard_mem (List.mem_of_getElem? selected) rest.guard_mem)
  | member memberIndex selected rest =>
      exact children_guard_mem (List.mem_of_getElem? selected) rest.guard_mem
  | body rest => exact rest.guard_mem
termination_by address.length

private theorem singleton_selected {A : Type} {value found : A} {index : Nat}
    (selected : [value][index]? = some found) : index = 0 ∧ found = value := by
  cases index with
  | zero => exact ⟨rfl, (Option.some.inj selected).symm⟩
  | succ index =>
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at selected
      cases selected

private theorem finish_site (symbol : String) (classes : List (List (List Nat))) (mapped : Expr Guard)
    {address : List Position} {index : Nat} {name : String} {guard : Guard} {children : List (Expr Guard)}
    (occurrence : RowAt (finish symbol classes mapped) address index (.mk name guard children)) :
    (address = [] ∧ index = 0 ∧ guard = eqGuard classes) ∨ guard ∈ guards mapped := by
  cases mapped with
  | empty | var => cases occurrence
  | union | binder => exact Or.inr occurrence.guard_mem
  | node rows =>
      cases rows with
      | nil => exact Or.inr occurrence.guard_mem
      | cons first rest =>
          cases first with
          | mk oldSymbol oldGuard oldChildren =>
              cases rest with
              | cons second tail => exact Or.inr occurrence.guard_mem
              | nil =>
                  change RowAt (.node [.mk symbol (eqGuard classes) oldChildren]) address index
                    (.mk name guard children) at occurrence
                  cases occurrence with
                  | node selected =>
                      obtain ⟨rfl, same⟩ := singleton_selected selected
                      cases same
                      exact Or.inl ⟨rfl, rfl, rfl⟩
                  | child rowIndex childIndex owner selected rest =>
                      obtain ⟨rfl, same⟩ := singleton_selected owner
                      cases same
                      have present := children_guard_mem (List.mem_of_getElem? selected) rest.guard_mem
                      exact Or.inr (List.mem_cons_of_mem oldGuard (List.mem_append_left [] present))

/-- A non-Top generalized guard occurs only at the single outer row of that original type. -/
theorem generalize_nonTop (typ : Ty) (constructors : List (String × Nat))
    {address : List Position} {index : Nat} {symbol : String} {guard : Guard} {children : List (Expr Guard)}
    (occurrence : RowAt (generalize (allTypes top constructors) typ) address index (.mk symbol guard children))
    (nonTop : guard ≠ top) : address = [] ∧ index = 0 ∧ guard = eqGuard (equalityClasses typ) := by
  rcases finish_site (rootSymbol typ) (equalityClasses typ) (replace (allTypes top constructors) typ) occurrence with
    outer | original
  · exact outer
  · rcases SourceSynthesisGeneralizeSyntax.replace_guards (allTypes top constructors) typ guard original with
      plain | inserted
    · exact False.elim (nonTop plain)
    · exact False.elim (nonTop (SourceSynthesisTypeSyntax.allTypes_guards top constructors guard inserted))

/-- Every proper interior literal row of the generalized original type has the exact Top guard. -/
theorem generalize_interior_top (typ : Ty) (constructors : List (String × Nat))
    {address : List Position} {index : Nat} {symbol : String} {guard : Guard} {children : List (Expr Guard)}
    (occurrence : RowAt (generalize (allTypes top constructors) typ) address index (.mk symbol guard children))
    (proper : address ≠ []) : guard = top := by
  by_cases plain : guard = top
  · exact plain
  · exact False.elim (proper (generalize_nonTop typ constructors occurrence plain).1)

/-- A generalized row is Top or retains its exact original outer type equality guard and site. -/
theorem generalize_site (typ : Ty) (constructors : List (String × Nat))
    {address : List Position} {index : Nat} {symbol : String} {guard : Guard} {children : List (Expr Guard)}
    (occurrence : RowAt (generalize (allTypes top constructors) typ) address index (.mk symbol guard children)) :
    guard = top ∨ address = [] ∧ index = 0 ∧ guard = eqGuard (equalityClasses typ) := by
  by_cases plain : guard = top
  · exact Or.inl plain
  · exact Or.inr (generalize_nonTop typ constructors occurrence plain)

/-- Every addressed rigid original type row has the exact Top guard. -/
theorem typeNode_top (typ : Ty)
    {address : List Position} {index : Nat} {symbol : String} {guard : Guard} {children : List (Expr Guard)}
    (occurrence : RowAt (typeNode top typ) address index (.mk symbol guard children)) : guard = top :=
  SourceSynthesisTypeSyntax.typeNode_guards top typ guard occurrence.guard_mem

/-- Every addressed original universe row has the exact Top guard, including binder-body rows. -/
theorem allTypes_top (constructors : List (String × Nat))
    {address : List Position} {index : Nat} {symbol : String} {guard : Guard} {children : List (Expr Guard)}
    (occurrence : RowAt (allTypes top constructors) address index (.mk symbol guard children)) : guard = top :=
  SourceSynthesisTypeSyntax.allTypes_guards top constructors guard occurrence.guard_mem

end MicroCFTA.SourceSynthesisTypeGuardSites
