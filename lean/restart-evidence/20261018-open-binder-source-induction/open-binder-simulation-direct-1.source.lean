import MicroCFTA.SourceCurrentOpenWeakSimulation

/-!
# Directional root simulation with mutual row children

An epsilon step retains one directional relation. Matched row children
retain both directions. Mutual root membership then gives every finite
observation without a global simulation for the converse relation.
Physical Empty agreement remains separate. The reader stays fixed.
This module does not supply a source or retained-writer instance.
-/
namespace MicroCFTA.SourceCurrentOpenPreorderSimulation
open InternedConstructorTemplates InternedEdgeResidency
open InternedBinderProtocol (Reference)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (ReferenceOrigin RowMatch Same)
open SourceCurrentOpenOriginSteps (Path path_of_reachable)
open Productivity (Reachable)
open Language

/-- A pair retains membership in both directions of the supplied relation. -/
def Mutual (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop := relation first second ∧ relation second first

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Roots simulate in one direction; ordered matched children retain mutual membership. -/
def Directed (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) : Prop :=
  ∀ first second, relation first second →
    (∀ name : Reference, first = .reference name → ReferenceOrigin reader [second] name) ∧
    (∀ row ∈ nodeEdges first, ∃ other, Origin reader [second] other ∧ RowMatch (Mutual relation) row other) ∧
    ∀ next ∈ successors reader first, ∃ later,
      Reachable (successors reader) [second] later ∧ relation next later

private theorem weak (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation) :
    SourceCurrentOpenWeakSimulation.Forward reader relation := by
  intro first second paired
  obtain ⟨references,rows,epsilon⟩ := simulation first second paired
  refine ⟨references,?_,epsilon⟩
  intro row member
  obtain ⟨other,found,fields⟩ := rows row member
  exact ⟨other,found,fields.1,fields.2.1,All₂.imp (fun _ _ pair => pair.1) fields.2.2⟩

/-- A counted left path has a reached right endpoint in the directional relation. -/
theorem Directed.path (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    {steps : Nat} {first second last : Value Symbol Guard} (paired : relation first second)
    (actual : Path reader steps first last) :
    ∃ later, Reachable (successors reader) [second] later ∧ relation last later :=
  (weak reader relation simulation).path reader relation paired actual

/-- Directional simulation preserves complete bare-reference observations. -/
theorem Directed.reference (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    {first second : Value Symbol Guard} (paired : relation first second) (name : Reference)
    (origin : ReferenceOrigin reader [first] name) : ReferenceOrigin reader [second] name :=
  (weak reader relation simulation).reference reader relation paired name origin

/-- Complete row origins retain full fields and mutual ordered child pairs. -/
theorem Directed.row (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    {first second : Value Symbol Guard} (paired : relation first second) (row : EdgeValue Symbol Guard)
    (origin : Origin reader [first] row) :
    ∃ other, Origin reader [second] other ∧ RowMatch (Mutual relation) row other := by
  obtain ⟨last,actual,physical⟩ := origin
  obtain ⟨source,member,steps,path⟩ := path_of_reachable reader [first] last actual
  obtain rfl := List.mem_singleton.mp member
  obtain ⟨later,reached,lastRelated⟩ := simulation.path reader relation paired path
  obtain ⟨other,found,fields⟩ := (simulation last later lastRelated).2.1 row physical
  exact ⟨other,found.from_seeds reader [later] [second]
    (fun value member => (List.mem_singleton.mp member) ▸ reached) other,fields⟩

/-- One directional simulation gives all finite observations for mutually related roots. -/
theorem same (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    (depth : Nat) :
    ∀ first second, Mutual relation first second → Same depth reader [first] [second] := by
  induction depth with
  | zero =>
      intro first second paired name
      exact ⟨simulation.reference reader relation paired.1 name,
        simulation.reference reader relation paired.2 name⟩
  | succ depth ih =>
      intro first second paired
      refine ⟨?_,?_,?_⟩
      · intro name
        exact ⟨simulation.reference reader relation paired.1 name,
          simulation.reference reader relation paired.2 name⟩
      · intro row origin
        obtain ⟨other,found,fields⟩ := simulation.row reader relation paired.1 row origin
        exact ⟨other,found,fields.1,fields.2.1,All₂.imp (fun _ _ pair => ih _ _ pair) fields.2.2⟩
      · intro row origin
        obtain ⟨other,found,fields⟩ := simulation.row reader relation paired.2 row origin
        exact ⟨other,found,fields.1,fields.2.1,All₂.imp (fun _ _ pair => ih _ _ pair) fields.2.2⟩

/-- Physical Empty agreement adds survival to the finite observations of mutual roots. -/
theorem related (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Directed reader relation)
    (first second : Value Symbol Guard) (paired : Mutual relation first second)
    (empty : first.referenceOf = .empty ↔ second.referenceOf = .empty) :
    SourceCurrentReaderObservations.Related reader first second :=
  ⟨empty,fun depth => same reader relation simulation depth first second paired⟩

end MicroCFTA.SourceCurrentOpenPreorderSimulation
