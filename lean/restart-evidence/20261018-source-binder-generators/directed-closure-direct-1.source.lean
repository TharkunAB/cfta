import MicroCFTA.SourceCurrentOpenPreorderSimulation

/-!
# Finite closure of directional simulations

Finite relation chains retain the actual epsilon, reference, and row clauses.
Matched rows keep their full fields and mutual ordered child relations.
Two independently proved simulations can supply alternative chain steps.
This module does not prove a source-binder instance or physical Empty agreement.
-/
namespace MicroCFTA.SourceCurrentDirectedClosure
open InternedConstructorTemplates InternedEdgeResidency
open InternedBinderProtocol (Reference)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (ReferenceOrigin RowMatch)
open SourceCurrentOpenOriginSteps (Path path_of_reachable)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open Productivity (Reachable)
open Language

universe u

/-- A finite sequence has zero or more steps in the supplied relation. -/
inductive Closure {Item : Type u} (relation : Item → Item → Prop) : Item → Item → Prop where
  | refl (value : Item) : Closure relation value value
  | step {first middle last : Item} : relation first middle → Closure relation middle last →
      Closure relation first last

/-- Each supplied relation step is a finite chain. -/
theorem Closure.single {relation : Item → Item → Prop} {first second : Item}
    (paired : relation first second) : Closure relation first second := .step paired (.refl second)

/-- Finite relation chains compose at their exact common endpoint. -/
theorem Closure.trans {relation : Item → Item → Prop} {first middle last : Item}
    (left : Closure relation first middle) (right : Closure relation middle last) :
    Closure relation first last := by
  induction left with
  | refl => exact right
  | step paired tail ih => exact .step paired (ih right)

/-- Inclusion of generating steps preserves every finite chain. -/
theorem Closure.mono {firstRelation secondRelation : Item → Item → Prop}
    (included : ∀ first second, firstRelation first second → secondRelation first second)
    {first second : Item} (chain : Closure firstRelation first second) :
    Closure secondRelation first second := by
  induction chain with
  | refl value => exact .refl value
  | step paired tail ih => exact .step (included _ _ paired) ih

private theorem all_refl (values : List (Value Symbol Guard)) :
    All₂ (Mutual (Closure relation)) values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons ⟨.refl value,.refl value⟩ ih

private theorem all_compose {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    {first middle last : List (Value Symbol Guard)}
    (left : All₂ (Mutual relation) first middle)
    (right : All₂ (Mutual (Closure relation)) middle last) :
    All₂ (Mutual (Closure relation)) first last := by
  induction left generalizing last with
  | nil => cases right; exact .nil
  | cons pair rest ih =>
      cases right with
      | cons next later =>
          exact .cons ⟨.step pair.1 next.1,next.2.trans (.single pair.2)⟩ (ih later)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem path_transfer (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    {first second : Value Symbol Guard} (chain : Closure relation first second)
    {last : Value Symbol Guard} (actual : Reachable (successors reader) [first] last) :
    ∃ later, Reachable (successors reader) [second] later ∧ Closure relation last later := by
  induction chain generalizing last with
  | refl => exact ⟨last,actual,.refl last⟩
  | @step first middle second paired tail ih =>
      obtain ⟨source,member,steps,path⟩ := path_of_reachable reader [first] last actual
      obtain rfl := List.mem_singleton.mp member
      obtain ⟨next,reached,related⟩ := simulation.path reader relation paired path
      obtain ⟨later,finished,rest⟩ := ih reached
      exact ⟨later,finished,.step related rest⟩

private theorem reference_transfer (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    {first second : Value Symbol Guard} (chain : Closure relation first second) (name : Reference)
    (actual : ReferenceOrigin reader [first] name) : ReferenceOrigin reader [second] name := by
  induction chain with
  | refl => exact actual
  | step paired tail ih => exact ih (simulation.reference reader relation paired name actual)

private theorem row_transfer (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    {first second : Value Symbol Guard} (chain : Closure relation first second)
    (row : EdgeValue Symbol Guard) (actual : Origin reader [first] row) :
    ∃ other, Origin reader [second] other ∧ RowMatch (Mutual (Closure relation)) row other := by
  induction chain generalizing row with
  | refl => exact ⟨row,actual,rfl,rfl,all_refl row.children⟩
  | step paired tail ih =>
      obtain ⟨next,reached,fields⟩ := simulation.row reader relation paired row actual
      obtain ⟨other,finished,later⟩ := ih next reached
      exact ⟨other,finished,fields.1.trans later.1,fields.2.1.trans later.2.1,
        all_compose fields.2.2 later.2.2⟩

/-- Alternative steps from two actual simulations retain the same local clauses. -/
theorem or_directed (reader : State Symbol Guard)
    (first second : Value Symbol Guard → Value Symbol Guard → Prop)
    (left : Directed reader first) (right : Directed reader second) :
    Directed reader (fun a b => first a b ∨ second a b) := by
  intro a b paired
  rcases paired with paired | paired
  · obtain ⟨references,rows,epsilon⟩ := left a b paired
    refine ⟨references,?_,?_⟩
    · intro row member
      obtain ⟨other,origin,fields⟩ := rows row member
      exact ⟨other,origin,fields.1,fields.2.1,
        All₂.imp (fun _ _ pair => ⟨Or.inl pair.1,Or.inl pair.2⟩) fields.2.2⟩
    · intro next member
      obtain ⟨later,reached,related⟩ := epsilon next member
      exact ⟨later,reached,Or.inl related⟩
  · obtain ⟨references,rows,epsilon⟩ := right a b paired
    refine ⟨references,?_,?_⟩
    · intro row member
      obtain ⟨other,origin,fields⟩ := rows row member
      exact ⟨other,origin,fields.1,fields.2.1,
        All₂.imp (fun _ _ pair => ⟨Or.inr pair.1,Or.inr pair.2⟩) fields.2.2⟩
    · intro next member
      obtain ⟨later,reached,related⟩ := epsilon next member
      exact ⟨later,reached,Or.inr related⟩

/-- Reflexive transitive closure preserves actual directional simulation. -/
theorem directed (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation) :
    Directed reader (Closure relation) := by
  intro first second chain
  refine ⟨?_,?_,?_⟩
  · intro name equal
    exact reference_transfer reader relation simulation chain name (equal ▸ .seed List.mem_cons_self)
  · intro row member
    exact row_transfer reader relation simulation chain row ⟨first,.seed List.mem_cons_self,member⟩
  · intro next member
    exact path_transfer reader relation simulation chain (.step (.seed List.mem_cons_self) member)

end MicroCFTA.SourceCurrentDirectedClosure
