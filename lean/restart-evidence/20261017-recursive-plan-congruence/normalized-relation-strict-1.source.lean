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
inductive Related : Syntax Symbol Guard → List (Value Symbol Guard) →
    Syntax Symbol Guard → List (Value Symbol Guard) → Prop where
  | empty : Related .empty firstInputs .empty secondInputs
  | var (same : firstInputs[left]?.getD .empty = secondInputs[right]?.getD .empty) :
      Related (.var left) firstInputs (.var right) secondInputs
  | node (rows : RowsRelated first firstInputs second secondInputs) :
      Related (.node first) firstInputs (.node second) secondInputs
  | union (members : ManyRelated first firstInputs second secondInputs) :
      Related (.union first) firstInputs (.union second) secondInputs
  | binder (bodies : ∀ name : Reference,
      Related first (.reference name :: firstInputs) second (.reference name :: secondInputs)) :
      Related (.binder smart first) firstInputs (.binder smart second) secondInputs

/-- Children and union members relate in their original order. -/
inductive ManyRelated : List (Syntax Symbol Guard) → List (Value Symbol Guard) →
    List (Syntax Symbol Guard) → List (Value Symbol Guard) → Prop where
  | nil : ManyRelated [] firstInputs [] secondInputs
  | cons (head : Related first firstInputs second secondInputs)
      (tail : ManyRelated rest firstInputs remaining secondInputs) :
      ManyRelated (first :: rest) firstInputs (second :: remaining) secondInputs

/-- A row retains its full symbol and guard and relates all children in order. -/
inductive RowRelated : EdgeSyntax Symbol Guard → List (Value Symbol Guard) →
    EdgeSyntax Symbol Guard → List (Value Symbol Guard) → Prop where
  | mk (children : ManyRelated first firstInputs second secondInputs) :
      RowRelated (.mk symbol guard first) firstInputs (.mk symbol guard second) secondInputs

/-- Every row occurrence has a related occurrence on the other side. -/
inductive RowsRelated : List (EdgeSyntax Symbol Guard) → List (Value Symbol Guard) →
    List (EdgeSyntax Symbol Guard) → List (Value Symbol Guard) → Prop where
  | mk (forward : ∀ row ∈ first, ∃ other ∈ second, RowRelated row firstInputs other secondInputs)
      (backward : ∀ row ∈ second, ∃ other ∈ first, RowRelated other firstInputs row secondInputs) :
      RowsRelated first firstInputs second secondInputs
end

end MicroCFTA.SourceCurrentNormalizedPlanRelation
