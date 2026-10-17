import MicroCFTA.InternedFreshOrdinaryPlanEquivalence

/-!
# Recursive plans with normalized node rows

Node rows can differ in order and multiplicity at every nested depth.
Children and union alternatives retain their order. Binder bodies relate
under every common reference argument. The relation contains no execution
or desired result equation.
-/
namespace MicroCFTA.SourceCurrentNormalizedPlanRelation
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedBinderProtocol (Reference)

mutual
/-- Plans retain lexical values and constructor structure while normalizing node row sets. -/
def Related (first : Syntax Symbol Guard) (firstInputs : List (Value Symbol Guard))
    (second : Syntax Symbol Guard) (secondInputs : List (Value Symbol Guard)) : Prop :=
  match first, second with
  | .empty, .empty => True
  | .var left, .var right => firstInputs[left]?.getD .empty = secondInputs[right]?.getD .empty
  | .node left, .node right => RowsRelated left firstInputs right secondInputs
  | .union left, .union right => ManyRelated left firstInputs right secondInputs
  | .binder leftSmart left, .binder rightSmart right =>
      leftSmart = rightSmart ∧ ∀ name : Reference,
        Related left (.reference name :: firstInputs) right (.reference name :: secondInputs)
  | _, _ => False
termination_by sizeOf first

/-- Children and union members relate in their original order. -/
def ManyRelated (first : List (Syntax Symbol Guard)) (firstInputs : List (Value Symbol Guard))
    (second : List (Syntax Symbol Guard)) (secondInputs : List (Value Symbol Guard)) : Prop :=
  match first, second with
  | [], [] => True
  | left :: rest, right :: remaining =>
      Related left firstInputs right secondInputs ∧ ManyRelated rest firstInputs remaining secondInputs
  | _, _ => False
termination_by sizeOf first

/-- A row retains its full symbol and guard and relates all children in order. -/
def RowRelated (first : EdgeSyntax Symbol Guard) (firstInputs : List (Value Symbol Guard))
    (second : EdgeSyntax Symbol Guard) (secondInputs : List (Value Symbol Guard)) : Prop :=
  match first, second with
  | .mk leftSymbol leftGuard left, .mk rightSymbol rightGuard right =>
      leftSymbol = rightSymbol ∧ leftGuard = rightGuard ∧ ManyRelated left firstInputs right secondInputs
termination_by sizeOf first

/-- Every row occurrence has a related occurrence on the other side. -/
def RowsRelated (first : List (EdgeSyntax Symbol Guard)) (firstInputs : List (Value Symbol Guard))
    (second : List (EdgeSyntax Symbol Guard)) (secondInputs : List (Value Symbol Guard)) : Prop :=
  (∀ row, ∀ (_ : row ∈ first), ∃ other, ∃ (_ : other ∈ second), RowRelated row firstInputs other secondInputs) ∧
    (∀ row, ∀ (_ : row ∈ second), ∃ other, ∃ (_ : other ∈ first), RowRelated other firstInputs row secondInputs)
termination_by sizeOf first
decreasing_by all_goals exact List.sizeOf_lt_of_mem (by assumption)
end

end MicroCFTA.SourceCurrentNormalizedPlanRelation
