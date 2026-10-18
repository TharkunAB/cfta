import MicroCFTA.SourceCurrentRetainedMuDirectedCase
import MicroCFTA.SourceCurrentSourceDirectedCases
import MicroCFTA.SourceCurrentDirectedClosure

/-!
# Literal local clauses through source normalization

Union normalization can expose rows below another union. Literal clauses
therefore retain all original root references, rows and Mu atoms. Actual
Mu successors remain separate from literal inclusion. Finite source and
normalization chains supply relation membership. This module does not
assert that every source generator or every such chain is Directed.
-/
namespace MicroCFTA.SourceCurrentLiteralLocalSimulation
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedEdgeResidency (nodeEdges)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentSourceDirectedCases (Below Local)
open SourceCurrentRetainedMuDirectedCase (Generated)
open SourceCurrentOpenObservations (ReferenceOrigin RowMatch)
open SourceCurrentOpenPreorderSimulation (Mutual)
open SourceCurrentDirectedClosure (Closure)
open MergedFreshOrdinaryGraph (Origin successors)
open Productivity (Reachable)
open SourceEqualityRequiredCache (Ordinary)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Finite chains retain actual source generators and one-way literal normalization fragments. -/
abbrev Relation (reader : State Symbol Guard) : Value Symbol Guard → Value Symbol Guard → Prop :=
  Closure (fun first second => Generated reader first second ∨ Below first second)

/-- Literal references, full rows and actual Mu successors transfer at one fixed reader. -/
def Clauses (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop :=
  (∀ name : Reference, Literal first (.reference name) → ReferenceOrigin reader [second] name) ∧
  (∀ row, Row first row → ∃ other, Origin reader [second] other ∧ RowMatch (Mutual relation) row other) ∧
  ∀ (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard),
    Literal first (.mu entry body depth ordinary) →
    ∀ next ∈ successors reader (.mu entry body depth ordinary),
      ∃ later, Reachable (successors reader) [second] later ∧ relation next later

private theorem literal_path (reader : State Symbol Guard) {root atom : Value Symbol Guard}
    (found : Literal root atom) : Reachable (successors reader) [root] atom := by
  induction found with
  | reference | mu => exact .seed List.mem_cons_self
  | @union entry members level free value atom member found ih =>
      exact EpsilonUnion.reach_trans _ _ value atom (.step (.seed List.mem_cons_self) member) ih

private theorem row_origin (reader : State Symbol Guard) {root : Value Symbol Guard}
    {row : EdgeValue Symbol Guard} (found : Row root row) : Origin reader [root] row := by
  induction found with
  | node member => exact ⟨_, .seed List.mem_cons_self, member⟩
  | @union entry members level free value row member found ih =>
      exact ih.from_seeds reader [value] [.union entry members level free]
        (fun current present => (List.mem_singleton.mp present) ▸
          Reachable.step (Reachable.seed List.mem_cons_self) member) row

private theorem all_refl (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (reflexive : ∀ value, relation value value) (values : List (Value Symbol Guard)) :
    All₂ (Mutual relation) values values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih => exact .cons ⟨reflexive value, reflexive value⟩ ih

/-- Exact literal inclusion supplies every literal clause without a source simulation premise. -/
theorem below (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (reflexive : ∀ value, relation value value) (first second : Value Symbol Guard)
    (included : Below first second) : Clauses reader relation first second := by
  refine ⟨?_, ?_, ?_⟩
  · intro name found
    exact literal_path reader (included.1 _ found)
  · intro row found
    exact ⟨row, row_origin reader (included.2 row found), rfl, rfl, all_refl relation reflexive row.children⟩
  · intro entry body depth ordinary found next member
    exact ⟨next, .step (literal_path reader (included.1 _ found)) member, reflexive next⟩

/-- Ordinary local endpoints have no additional literal reference or Mu obligations. -/
theorem of_ordinary (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) (ordinary : Ordinary first)
    (local : Local reader relation first second) : Clauses reader relation first second := by
  refine ⟨?_, ?_, ?_⟩
  · intro name found
    cases first <;> try cases ordinary <;> cases found
  · intro row found
    apply local.2.1 row
    cases first with
    | empty => cases found
    | node entry rows depth free => exact (SourceCurrentLiteralRootParts.row_node entry rows depth free row).mp found
    | reference | union | mu => cases ordinary
  · intro entry body depth ordinaryBody found
    cases first <;> try cases ordinary <;> cases found

/-- Inclusion of child and successor relations retains all literal clauses. -/
theorem mono (reader : State Symbol Guard)
    (firstRelation secondRelation : Value Symbol Guard → Value Symbol Guard → Prop)
    (included : ∀ first second, firstRelation first second → secondRelation first second)
    {first second : Value Symbol Guard} (clauses : Clauses reader firstRelation first second) :
    Clauses reader secondRelation first second := by
  refine ⟨clauses.1, ?_, ?_⟩
  · intro row found
    obtain ⟨other, origin, fields⟩ := clauses.2.1 row found
    exact ⟨other, origin, fields.1, fields.2.1,
      All₂.imp (fun _ _ pair => ⟨included _ _ pair.1, included _ _ pair.2⟩) fields.2.2⟩
  · intro entry body depth ordinary found next member
    obtain ⟨later, reached, pair⟩ := clauses.2.2 entry body depth ordinary found next member
    exact ⟨later, reached, included _ _ pair⟩

private theorem compose_children {first middle last : List (Value Symbol Guard)}
    (left : All₂ (Mutual (Relation reader)) first middle)
    (right : All₂ (Mutual Below) middle last) : All₂ (Mutual (Relation reader)) first last := by
  induction left generalizing last with
  | nil => cases right; exact .nil
  | cons pair tail ih =>
      cases right with
      | cons next rest =>
          exact .cons ⟨pair.1.trans (.single (.inr next.1)), (.single (.inr next.2)).trans pair.2⟩ (ih rest)

/-- A genuine one-way normalization fragment retains each transferred literal observation. -/
theorem post_below (reader : State Symbol Guard) {first middle last : Value Symbol Guard}
    (clauses : Clauses reader (Relation reader) first middle) (included : Below middle last) :
    Clauses reader (Relation reader) first last := by
  have directed := SourceCurrentSourceDirectedCases.below_directed reader
  refine ⟨?_, ?_, ?_⟩
  · intro name found
    exact directed.reference reader Below included name (clauses.1 name found)
  · intro row found
    obtain ⟨other, origin, fields⟩ := clauses.2.1 row found
    obtain ⟨final, reached, later⟩ := directed.row reader Below included other origin
    exact ⟨final, reached, fields.1.trans later.1, fields.2.1.trans later.2.1,
      compose_children fields.2.2 later.2.2⟩
  · intro entry body depth ordinary found next member
    obtain ⟨endpoint, reached, pair⟩ := clauses.2.2 entry body depth ordinary found next member
    obtain ⟨source, present, steps, path⟩ := SourceCurrentOpenOriginSteps.path_of_reachable reader [middle] endpoint reached
    obtain rfl := List.mem_singleton.mp present
    obtain ⟨final, finished, fragment⟩ := directed.path reader Below included path
    exact ⟨final, finished, pair.trans (.single (.inr fragment))⟩

/-- Literal clauses and actual chain membership supply the immediate local simulation endpoint. -/
theorem local (reader : State Symbol Guard) {first second : Value Symbol Guard}
    (related : Relation reader first second) (clauses : Clauses reader (Relation reader) first second) :
    Local reader (Relation reader) first second := by
  refine ⟨?_, ?_, ?_⟩
  · intro name same
    subst first
    exact clauses.1 name (.reference name)
  · intro row member
    apply clauses.2.1 row
    cases first with
    | node entry rows depth free => exact .node member
    | empty | reference | union | mu => cases member
  · intro next member
    cases first with
    | empty | reference | node => cases member
    | union entry members depth free =>
        have fragment : Below next (.union entry members depth free) :=
          ⟨fun _ found => .union member found, fun _ found => .union member found⟩
        exact ⟨second, .seed List.mem_cons_self, (Closure.single (.inr fragment)).trans related⟩
    | mu entry body depth ordinary => exact clauses.2.2 entry body depth ordinary (.mu entry body depth ordinary) next member

end MicroCFTA.SourceCurrentLiteralLocalSimulation
