import MicroCFTA.InternedFreeNameConstructors
import MicroCFTA.InternedNestedProfiles

/-!
# Ordered free-name composition for actual source constructors

Free-name comparison uses membership. It does not require canonical
records to retain the order of a later equivalent source expression.
-/
namespace MicroCFTA.InternedFreeNameComposition
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedStoredMuOrigins InternedRootProfile InternedProfileSemantics
open InternedOccurrenceObservations (Paired)
open InternedBinderProtocol (Reference)

/-- Two free-name lists describe the same set of names. -/
def Same (first second : List Reference) : Prop := ∀ name, name ∈ first ↔ name ∈ second

/-- Ordered source values have their specified free-name sets. -/
abbrev Matches (values : List (Value Symbol Guard)) (names : List (List Reference)) : Prop :=
  Paired (fun value expected => Same value.free expected) values names

/-- Flattening matched children preserves exactly their free names. -/
theorem many_matched {values : List (Value Symbol Guard)} {names : List (List Reference)}
    (matched : Matches values names) : Same (values.flatMap Value.free) names.flatten := by
  induction matched with
  | nil => exact fun _ => Iff.rfl
  | cons head tail ih =>
      intro name
      simp only [List.flatMap_cons, List.flatten_cons, List.mem_append]
      exact or_congr (head name) (ih name)

/-- Live source edges contribute all free names of their ordered children. -/
def liveFree (edges : List (EdgeValue Symbol Guard)) : List Reference :=
  edges.flatMap fun edge =>
    if edge.children.all (fun child => !isEmpty (profile child))
    then edge.children.flatMap Value.free else []

/-- Actual empty-child tests agree with the profile tests of each available child. -/
theorem live_children (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (available : Values state values) :
    values.all (fun child => !isEmpty (profile child)) =
      !(values.any (fun child => child.referenceOf == .empty)) := by
  rw [List.not_any_eq_all_not]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  apply forall_congr'
  intro child
  apply forall_congr'
  intro member
  rw [InternedRootProfileNode.isEmpty_profile child state normal.proper (available child member)]

/-- The source node has exactly the names contributed by its live edges. -/
theorem node_free [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (normal : Normal state) (available : Edges state edges) :
    Same (run (makeNode edges) state).1.free (liveFree edges) := by
  intro name
  rw [InternedFreeNameConstructors.node_membership edges state normal available name]
  simp only [liveFree, List.mem_flatMap]
  apply exists_congr
  intro edge
  apply and_congr_right
  intro member
  have children : Values state edge.children :=
    normal.facts.cached.edges edge.entry.key edge (available edge member)
  rw [live_children edge.children state normal children]
  cases decision : edge.children.any (fun child => child.referenceOf == .empty) <;>
    simp [List.mem_flatMap]

/-- The source union has exactly the names of its original operands. -/
theorem union_free [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : Normal state) (available : Values state values) :
    Same (run (makeUnion values) state).1.free (values.flatMap Value.free) := by
  intro name
  rw [InternedFreeNameConstructors.union_membership values state normal available name]
  exact List.mem_flatMap.symm

end MicroCFTA.InternedFreeNameComposition
