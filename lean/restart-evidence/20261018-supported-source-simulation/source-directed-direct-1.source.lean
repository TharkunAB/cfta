import MicroCFTA.SourceCurrentOpenPreorderSimulation
import MicroCFTA.SourceCurrentLiteralUnionParts
import MicroCFTA.SourceCurrentPublicationNodeRowSurvival
import MicroCFTA.SourceCurrentStoredNodeExpansion

/-!
# Local source cases for directional simulation

Literal inclusion supplies normalization fragments at one reader.
Actual node calls retain full rows and ordered child memberships.
Physical Empty agreement is required only where rows can be removed.
The general used-binder source simulation remains separate.
-/
namespace MicroCFTA.SourceCurrentSourceDirectedCases
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedEdgeResidency (nodeEdges)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedBinderProtocol (Reference)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open SourceCurrentOpenObservations (ReferenceOrigin RowMatch)
open SourceCurrentLiteralRootParts (Literal Row)
open MergedFreshOrdinaryGraph (Origin successors)
open Productivity (Reachable)

/-- Exact root atoms and full rows of the first value occur in the second value. -/
def Below (first second : Value Symbol Guard) : Prop :=
  (∀ atom, Literal first atom → Literal second atom) ∧
    ∀ row, Row first row → Row second row

/-- Literal inclusion retains each value. -/
theorem Below.refl (value : Value Symbol Guard) : Below value value := ⟨fun _ => id,fun _ => id⟩

/-- Literal inclusion composes without an observation premise. -/
theorem Below.trans {first middle last : Value Symbol Guard}
    (left : Below first middle) (right : Below middle last) : Below first last :=
  ⟨fun atom found => right.1 atom (left.1 atom found),fun row found => right.2 row (left.2 row found)⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One pair supplies the literal reference, physical row, and epsilon clauses. -/
def Local (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop :=
  (∀ name : Reference, first = .reference name → ReferenceOrigin reader [second] name) ∧
  (∀ row ∈ nodeEdges first, ∃ other, Origin reader [second] other ∧ RowMatch (Mutual relation) row other) ∧
  ∀ next ∈ successors reader first, ∃ later,
    Reachable (successors reader) [second] later ∧ relation next later

private theorem all_refl {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    (reflexive : ∀ value, relation value value) (values : List (Value Symbol Guard)) : All₂ relation values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (reflexive value) ih

private theorem literal_path (reader : State Symbol Guard) {root atom : Value Symbol Guard}
    (found : Literal root atom) : Reachable (successors reader) [root] atom := by
  induction found with
  | reference | mu => exact .seed List.mem_cons_self
  | @union entry members level free value atom member found ih =>
      exact EpsilonUnion.reach_trans _ _ value atom
        (.step (.seed List.mem_cons_self) member) ih

private theorem row_origin (reader : State Symbol Guard) {root : Value Symbol Guard}
    {row : EdgeValue Symbol Guard} (found : Row root row) : Origin reader [root] row := by
  induction found with
  | node member => exact ⟨_,.seed List.mem_cons_self,member⟩
  | @union entry members level free value row member found ih =>
      exact ih.from_seeds reader [value] [.union entry members level free]
        (fun current present => (List.mem_singleton.mp present) ▸
          Reachable.step (Reachable.seed List.mem_cons_self) member) row

/-- Exact literal inclusion is a directional simulation, including actual Mu unfolding. -/
theorem below_directed (reader : State Symbol Guard) : Directed reader (Below (Symbol := Symbol) (Guard := Guard)) := by
  intro first second included
  refine ⟨?_,?_,?_⟩
  · intro name same
    subst first
    exact literal_path reader (included.1 _ (.reference name))
  · intro row member
    have literal : Row first row := by
      cases first <;> try cases member
      exact .node member
    exact ⟨row,row_origin reader (included.2 row literal),rfl,rfl,
      all_refl (fun value => ⟨Below.refl value,Below.refl value⟩) row.children⟩
  · intro next member
    cases first with
    | empty | reference | node => cases member
    | union entry members level free =>
        refine ⟨second,.seed List.mem_cons_self,?_,?_⟩
        · intro atom found
          exact included.1 atom (.union member found)
        · intro row found
          exact included.2 row (.union member found)
    | mu entry body depth ordinary =>
        have reached := literal_path reader (included.1 _ (.mu entry body depth ordinary))
        exact ⟨next,.step reached member,Below.refl next⟩

/-- Equality gives a local clause when the child relation contains equality. -/
theorem equal (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (reflexive : ∀ value, relation value value) (value : Value Symbol Guard) : Local reader relation value value := by
  refine ⟨?_,?_,?_⟩
  · intro name same
    exact same ▸ Reachable.seed List.mem_cons_self
  · intro row member
    exact ⟨row,⟨value,.seed List.mem_cons_self,member⟩,rfl,rfl,
      all_refl (fun value => ⟨reflexive value,reflexive value⟩) row.children⟩
  · intro next member
    exact ⟨next,.step (.seed List.mem_cons_self) member,reflexive next⟩

/-- Each initial member is a literal fragment of the actual normalized union result. -/
theorem union_member (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (normal : Normal before) (available : Values before values)
    (value : Value Symbol Guard) (member : value ∈ values) :
    Below value (run (makeUnion values) before).1 := by
  constructor
  · intro atom found
    exact (SourceCurrentLiteralUnionParts.literal before normal.facts values available atom).mpr ⟨value,member,found⟩
  · intro row found
    exact (SourceCurrentLiteralUnionParts.row before normal.facts normal.live values available row).mpr ⟨value,member,found⟩

end MicroCFTA.SourceCurrentSourceDirectedCases
