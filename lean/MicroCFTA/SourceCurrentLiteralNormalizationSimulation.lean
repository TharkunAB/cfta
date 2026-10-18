import MicroCFTA.SourceCurrentLiteralLocalSimulation

/-!
# Literal normalization around one source relation step

A relation pair can contain at most one source step. Literal inclusion can
precede or follow that step. Full literal clauses for each source step
then prove directional simulation of this relation. No chain of source
steps or observation equality is assumed.
-/
namespace MicroCFTA.SourceCurrentLiteralNormalizationSimulation
open Cache Language InternedConstructorTemplates
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentSourceDirectedCases (Below)
open SourceCurrentLiteralLocalSimulation (Clauses)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open SourceCurrentOpenObservations (RowMatch)
open MergedFreshOrdinaryGraph (Origin successors)
open Productivity (Reachable)

/-- Literal normalization surrounds at most one supplied source relation pair. -/
def Relation (source : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop :=
  Below first second ∨ ∃ left right, Below first left ∧ source left right ∧ Below right second

/-- A literal inclusion before the relation does not add a source step. -/
theorem Relation.pre {source : Value Symbol Guard → Value Symbol Guard → Prop}
    {first middle last : Value Symbol Guard} (included : Below first middle)
    (related : Relation source middle last) : Relation source first last := by
  rcases related with old | ⟨left,right,before,paired,after⟩
  · exact .inl (included.trans old)
  · exact .inr ⟨left,right,included.trans before,paired,after⟩

/-- A literal inclusion after the relation does not add a source step. -/
theorem Relation.post {source : Value Symbol Guard → Value Symbol Guard → Prop}
    {first middle last : Value Symbol Guard} (related : Relation source first middle)
    (included : Below middle last) : Relation source first last := by
  rcases related with old | ⟨left,right,before,paired,after⟩
  · exact .inl (old.trans included)
  · exact .inr ⟨left,right,before,paired,after.trans included⟩

private theorem literal_path [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) {root atom : Value Symbol Guard} (found : Literal root atom) :
    Reachable (successors reader) [root] atom := by
  induction found with
  | reference | mu => exact .seed List.mem_cons_self
  | @union entry members level free value atom member found ih =>
      exact EpsilonUnion.reach_trans _ _ value atom
        (.step (.seed List.mem_cons_self) member) ih

private theorem pre_clauses [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    {first middle last : Value Symbol Guard} (included : Below first middle)
    (clauses : Clauses reader relation middle last) : Clauses reader relation first last := by
  exact ⟨fun name found => clauses.1 name (included.1 _ found),
    fun row found => clauses.2.1 row (included.2 row found),
    fun entry body depth ordinary found => clauses.2.2 entry body depth ordinary (included.1 _ found)⟩

private theorem compose_children {source : Value Symbol Guard → Value Symbol Guard → Prop}
    {first middle last : List (Value Symbol Guard)}
    (left : All₂ (Mutual (Relation source)) first middle)
    (right : All₂ (Mutual Below) middle last) :
    All₂ (Mutual (Relation source)) first last := by
  induction left generalizing last with
  | nil => cases right; exact .nil
  | cons pair tail ih =>
      cases right with
      | cons next rest => exact .cons ⟨pair.1.post next.1, Relation.pre next.2 pair.2⟩ (ih rest)

private theorem post_clauses [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) (source : Value Symbol Guard → Value Symbol Guard → Prop)
    {first middle last : Value Symbol Guard}
    (clauses : Clauses reader (Relation source) first middle) (included : Below middle last) :
    Clauses reader (Relation source) first last := by
  have normalization := SourceCurrentSourceDirectedCases.below_directed reader
  refine ⟨?_,?_,?_⟩
  · intro name found
    exact normalization.reference reader Below included name (clauses.1 name found)
  · intro row found
    obtain ⟨other,origin,fields⟩ := clauses.2.1 row found
    obtain ⟨final,reached,later⟩ := normalization.row reader Below included other origin
    exact ⟨final,reached,fields.1.trans later.1,fields.2.1.trans later.2.1,
      compose_children fields.2.2 later.2.2⟩
  · intro entry body depth ordinary found next member
    obtain ⟨endpoint,reached,related⟩ := clauses.2.2 entry body depth ordinary found next member
    obtain ⟨initial,present,steps,path⟩ :=
      SourceCurrentOpenOriginSteps.path_of_reachable reader [middle] endpoint reached
    obtain rfl := List.mem_singleton.mp present
    obtain ⟨final,finished,fragment⟩ := normalization.path reader Below included path
    exact ⟨final,finished,related.post fragment⟩

private theorem clauses [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) (source : Value Symbol Guard → Value Symbol Guard → Prop)
    (steps : ∀ first second, source first second → Clauses reader (Relation source) first second)
    {first second : Value Symbol Guard} (related : Relation source first second) :
    Clauses reader (Relation source) first second := by
  rcases related with included | ⟨left,right,before,paired,after⟩
  · exact SourceCurrentLiteralLocalSimulation.below reader (Relation source)
      (fun value => .inl (Below.refl value)) first second included
  · exact post_clauses reader source (pre_clauses reader (Relation source) before (steps _ _ paired)) after

/-- Literal clauses for genuine source pairs suffice when normalization adds no second source pair. -/
theorem directed [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) (source : Value Symbol Guard → Value Symbol Guard → Prop)
    (steps : ∀ first second, source first second → Clauses reader (Relation source) first second) :
    Directed reader (Relation source) := by
  intro first second related
  have complete := clauses reader source steps related
  refine ⟨?_,?_,?_⟩
  · intro name same
    subst first
    exact complete.1 name (.reference name)
  · intro row member
    apply complete.2.1 row
    cases first with
    | node entry rows depth free => exact .node member
    | empty | reference | union | mu => cases member
  · intro next member
    cases first with
    | empty | reference | node => cases member
    | union entry members depth free =>
        have included : Below next (.union entry members depth free) :=
          ⟨fun _ found => .union member found,fun _ found => .union member found⟩
        exact ⟨second,.seed List.mem_cons_self,Relation.pre included related⟩
    | mu entry body depth ordinary =>
        exact complete.2.2 entry body depth ordinary (.mu entry body depth ordinary) next member

end MicroCFTA.SourceCurrentLiteralNormalizationSimulation
