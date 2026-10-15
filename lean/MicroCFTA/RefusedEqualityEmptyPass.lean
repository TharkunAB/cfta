import MicroCFTA.EqualityReduction

/-!
# Empty refused classes in the equality pass

This model follows the new early return from main a22b2ad4. A refused class
can make every child empty after its secondary gate clears and a sound
emptiness query succeeds. Primitive projection and intersection laws supply
the class witness. Native calls, memo demand, and lazy partition effects
remain separate source obligations.
-/
namespace MicroCFTA.RefusedEqualityEmptyPass
open Language EqualityNormalize EqualityReduction

/-- The secondary gate controls whether the pass may query a refused class. -/
def emptyBelowEnd (ops : Operations Node Symbol) (secondary : List Node → Class → Bool)
    (oracle : Node → Bool) (nodes : List Node) (paths : Class) : Bool :=
  !(secondary nodes paths) && oracle (intersectList ops (paths.map (ops.project nodes)))

/-- Refused classes retain their original relative order. -/
def refusedClasses (ops : Operations Node Symbol) (classes : Constraints) (nodes : List Node) : Constraints :=
  classes.filter (ops.blocked nodes)

/-- The source checks refused classes before the selected-class path edits. -/
def pass [DecidableEq Node] (ops : Operations Node Symbol) (secondary : List Node → Class → Bool)
    (oracle : Node → Bool) (localClasses inherited : Constraints) (nodes : List Node) : List Node :=
  if localClasses = [] ∧ inherited = [] then nodes
  else if ops.contradictory localClasses inherited then nodes.map (fun _ => ops.empty)
  else if (refusedClasses ops localClasses nodes).any (emptyBelowEnd ops secondary oracle nodes) then
    nodes.map (fun _ => ops.empty)
  else
    let selected := selectedClasses ops localClasses nodes
    propagate ops (selected.foldr (reduceClass ops) (ops.requireAll selected.flatten nodes))

/-- A satisfied nontrivial class supplies an accepted common projection. -/
theorem class_common (ops : Operations Node Symbol) (laws : Laws ops) (nodes : List Node)
    (paths : Class) (active : Nontrivial paths) (term : Term Symbol)
    (accepted : Forest ops nodes term) (satisfied : ClassSat term paths) :
    ∃ subtree, ops.meaning (intersectList ops (paths.map (ops.project nodes))) subtree := by
  obtain ⟨left, leftMember, right, rightMember, different⟩ := active
  have active : Nontrivial paths := ⟨left, leftMember, right, rightMember, different⟩
  obtain ⟨subtree, found⟩ := class_member_exists term paths active satisfied left leftMember
  refine ⟨subtree, (intersectList_exact ops laws _ ?_ subtree).mpr ?_⟩
  · intro empty
    have member : ops.project nodes left ∈ paths.map (ops.project nodes) := List.mem_map.mpr ⟨left, leftMember, rfl⟩
    simp [empty] at member
  · intro projected member
    obtain ⟨path, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨value, leftValue, pathValue⟩ := class_pair_equal term paths active satisfied left path leftMember present
    have same : value = subtree := Option.some.inj (leftValue.symm.trans found)
    subst value
    exact laws.project nodes term path subtree (class_nonroot paths active term satisfied path present) accepted pathValue

/-- A sound oracle cannot reject any class satisfied by an accepted forest. -/
theorem refused_clear (ops : Operations Node Symbol) (laws : Laws ops)
    (secondary : List Node → Class → Bool) (oracle : Node → Bool)
    (sound : ∀ node, oracle node = true → ∀ term, ¬ops.meaning node term)
    (classes : Constraints) (active : Active classes) (nodes : List Node) (term : Term Symbol)
    (accepted : Forest ops nodes term) (satisfied : Satisfies term classes) :
    (refusedClasses ops classes nodes).any (emptyBelowEnd ops secondary oracle nodes) = false := by
  cases result : (refusedClasses ops classes nodes).any (emptyBelowEnd ops secondary oracle nodes) with
  | false => rfl
  | true =>
      obtain ⟨paths, member, rejected⟩ := List.any_eq_true.mp result
      have original : paths ∈ classes := (List.mem_filter.mp member).1
      obtain ⟨subtree, common⟩ := class_common ops laws nodes paths (active paths original) term accepted (satisfied paths original)
      have both := Bool.and_eq_true_iff.mp rejected
      exact False.elim (sound _ both.2 subtree common)

/-- Replacing each child by empty cannot add a forest term. -/
theorem empty_children_narrow (ops : Operations Node Symbol) (laws : Laws ops)
    (nodes : List Node) (term : Term Symbol) :
    Forest ops (nodes.map (fun _ => ops.empty)) term → Forest ops nodes term := by
  cases nodes with
  | nil => exact id
  | cons node nodes =>
      cases term with
      | node symbol children =>
          intro accepted
          cases accepted with
          | cons head tail => exact False.elim (laws.empty _ head)

/-- Every branch of the new pass narrows the original forest. -/
theorem pass_narrow [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (secondary : List Node → Class → Bool) (oracle : Node → Bool)
    (localClasses inherited : Constraints) (nodes : List Node) (term : Term Symbol) :
    Forest ops (pass ops secondary oracle localClasses inherited nodes) term → Forest ops nodes term := by
  unfold pass
  split
  · exact id
  · split
    · exact empty_children_narrow ops laws nodes term
    · split
      · exact empty_children_narrow ops laws nodes term
      · intro accepted
        exact laws.require_narrow _ nodes term
          (classes_narrow ops laws _ _ term ((propagate_exact ops laws _ term).mp accepted))

/-- The new early-empty branch retains every term satisfying both original constraint sets. -/
theorem pass_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (secondary : List Node → Class → Bool) (oracle : Node → Bool)
    (sound : ∀ node, oracle node = true → ∀ term, ¬ops.meaning node term)
    (localClasses inherited : Constraints) (active : Active localClasses) (nodes : List Node)
    (term : Term Symbol) (satisfied : Satisfies term localClasses ∧ Satisfies term inherited) :
    Forest ops (pass ops secondary oracle localClasses inherited nodes) term ↔ Forest ops nodes term := by
  constructor
  · exact pass_narrow ops laws secondary oracle localClasses inherited nodes term
  · intro accepted
    have clear := refused_clear ops laws secondary oracle sound localClasses active nodes term accepted satisfied.1
    have consistent : ops.contradictory localClasses inherited = false := by
      cases found : ops.contradictory localClasses inherited with
      | false => rfl
      | true => exact False.elim (laws.contradiction localClasses inherited term found satisfied)
    have old := (EqualityReduction.pass_exact ops laws localClasses inherited active
      (fun paths member => class_nonroot paths (active paths member) term (satisfied.1 paths member))
      nodes term satisfied).mpr accepted
    simpa only [pass, EqualityReduction.pass, consistent, clear, Bool.false_eq_true, ite_false] using old

end MicroCFTA.RefusedEqualityEmptyPass
