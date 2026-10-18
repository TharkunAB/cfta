import MicroCFTA.SourceCurrentOpenPreorderSimulation

set_option linter.all true

namespace MicroCFTA.OpenBinderSimulationFiniteSupport
open Cache Language InternedConstructorTemplates InternedEdgeResidency
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (ReferenceOrigin RowMatch)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open InternedBinderProtocol (Reference)
open Productivity (Reachable)

private def supportRelation (left right : List (Value Symbol Guard))
    (first second : Value Symbol Guard) (a b : Value Symbol Guard) : Prop :=
  a = b ∨ (a ∈ left ∧ b = second) ∨ (a ∈ right ∧ b = first)

private theorem finite_support_directed [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) (left right : List (Value Symbol Guard))
    (first second : Value Symbol Guard)
    (leftClosed : ∀ value ∈ left, ∀ next ∈ successors reader value, next ∈ left)
    (rightClosed : ∀ value ∈ right, ∀ next ∈ successors reader value, next ∈ right)
    (leftReferences : ∀ value ∈ left, ∀ name : Reference,
      value = .reference name → ReferenceOrigin reader [second] name)
    (rightReferences : ∀ value ∈ right, ∀ name : Reference,
      value = .reference name → ReferenceOrigin reader [first] name)
    (leftRows : ∀ value ∈ left, ∀ row ∈ nodeEdges value, Origin reader [second] row)
    (rightRows : ∀ value ∈ right, ∀ row ∈ nodeEdges value, Origin reader [first] row) :
    Directed reader (supportRelation left right first second) := by
  let relation := supportRelation left right first second
  have identity (row : EdgeValue Symbol Guard) : RowMatch (Mutual relation) row row := by
    refine ⟨rfl,rfl,?_⟩
    induction row.children with
    | nil => exact .nil
    | cons head tail ih => exact .cons ⟨Or.inl rfl,Or.inl rfl⟩ ih
  intro a b paired
  rcases paired with rfl | ⟨member,rfl⟩ | ⟨member,rfl⟩
  · refine ⟨?_,?_,?_⟩
    · intro name same
      cases same
      exact .seed List.mem_cons_self
    · intro row member
      exact ⟨row,⟨a,.seed List.mem_cons_self,member⟩,identity row⟩
    · intro next member
      exact ⟨next,.step (.seed List.mem_cons_self) member,Or.inl rfl⟩
  · refine ⟨leftReferences a member,?_,?_⟩
    · intro row present
      exact ⟨row,leftRows a member row present,identity row⟩
    · intro next present
      exact ⟨b,.seed List.mem_cons_self,Or.inr (Or.inl ⟨leftClosed a member next present,rfl⟩)⟩
  · refine ⟨rightReferences a member,?_,?_⟩
    · intro row present
      exact ⟨row,rightRows a member row present,identity row⟩
    · intro next present
      exact ⟨b,.seed List.mem_cons_self,Or.inr (Or.inr ⟨rightClosed a member next present,rfl⟩)⟩

end MicroCFTA.OpenBinderSimulationFiniteSupport
