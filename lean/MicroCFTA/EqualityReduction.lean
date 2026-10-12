import MicroCFTA.EqualityNarrowing
import MicroCFTA.SymbolicSmartRows

/-!
# Equality reduction passes and fixed-point execution

This model follows `reduceEqConstraints`: select safe local classes, require
their paths, edit every class in right-fold order, propagate empty children,
and repeat until the child identities stop changing. Primitive graph actions
have separate local contracts. No contract assumes correctness of a pass or
of its repeated execution.
-/

namespace MicroCFTA.EqualityReduction
open Language EqualityNormalize

/-- The node operations called by the source equality reduction loop. -/
structure Operations (Node Symbol : Type) where
  meaning : Node → Term Symbol → Prop
  empty : Node
  intersect : Node → Node → Node
  project : List Node → Path → Node
  requireAll : List Path → List Node → List Node
  editAll : List (Path × Node) → List Node → List Node
  blocked : List Node → Class → Bool
  contradictory : Constraints → Constraints → Bool

/-- A child list retains its complete ordered forest under the original constructor. -/
def Forest (ops : Operations Node Symbol) (nodes : List Node) : Term Symbol → Prop
  | .node _ children => All₂ ops.meaning nodes children

/-- Local graph laws required by the source loop. -/
structure Laws (ops : Operations Node Symbol) : Prop where
  empty : ∀ term, ¬ops.meaning ops.empty term
  intersect : ∀ left right term, ops.meaning (ops.intersect left right) term ↔ ops.meaning left term ∧ ops.meaning right term
  project : ∀ nodes term path subtree, path ≠ [] → Forest ops nodes term → term.atPath path = some subtree →
    ops.meaning (ops.project nodes path) subtree
  require_narrow : ∀ paths nodes term, Forest ops (ops.requireAll paths nodes) term → Forest ops nodes term
  require_keep : ∀ paths nodes term, Forest ops nodes term →
    (∀ path ∈ paths, ∃ subtree, term.atPath path = some subtree) → Forest ops (ops.requireAll paths nodes) term
  edit_narrow : ∀ edits nodes term, Forest ops (ops.editAll edits nodes) term → Forest ops nodes term
  edit_keep : ∀ edits nodes term, Forest ops nodes term →
    (∀ path target, (path, target) ∈ edits → ∀ subtree, term.atPath path = some subtree → ops.meaning target subtree) →
    Forest ops (ops.editAll edits nodes) term
  contradiction : ∀ localClasses inherited (term : Term Symbol), ops.contradictory localClasses inherited = true →
    ¬(Satisfies term localClasses ∧ Satisfies term inherited)

/-- The source uses the first node as the seed for a right-fold intersection. -/
def intersectList (ops : Operations Node Symbol) : List Node → Node
  | [] => ops.empty
  | node :: nodes => nodes.foldr ops.intersect node

/-- The seeded source fold is the intersection of all its listed languages. -/
theorem fold_intersection (ops : Operations Node Symbol) (laws : Laws ops)
    (nodes : List Node) (seed : Node) (term : Term Symbol) :
    ops.meaning (nodes.foldr ops.intersect seed) term ↔ ops.meaning seed term ∧ ∀ node ∈ nodes, ops.meaning node term := by
  induction nodes with
  | nil => simp
  | cons node nodes ih =>
    simp only [List.foldr_cons, laws.intersect, ih, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨head, seed, tail⟩; exact ⟨seed, head, tail⟩
    · rintro ⟨seed, head, tail⟩; exact ⟨head, seed, tail⟩

/-- No class intersection drops a term common to every projected node. -/
theorem intersectList_exact (ops : Operations Node Symbol) (laws : Laws ops)
    (nodes : List Node) (nonempty : nodes ≠ []) (term : Term Symbol) :
    ops.meaning (intersectList ops nodes) term ↔ ∀ node ∈ nodes, ops.meaning node term := by
  cases nodes with
  | nil => exact False.elim (nonempty rfl)
  | cons node nodes => simpa [intersectList] using fold_intersection ops laws nodes node term

/-- The complete list of simultaneous source edits for one class. -/
def classEdits (ops : Operations Node Symbol) (paths : Class) (nodes : List Node) : List (Path × Node) :=
  paths.map fun path => (path, intersectList ops ((EqualityNarrowing.others paths path).map (ops.project nodes)))

/-- Apply one equality class using projections from the same input child list. -/
def reduceClass (ops : Operations Node Symbol) (paths : Class) (nodes : List Node) : List Node :=
  ops.editAll (classEdits ops paths nodes) nodes

/-- Each class edit is a narrowing operation. -/
theorem reduceClass_narrow (ops : Operations Node Symbol) (laws : Laws ops)
    (paths : Class) (nodes : List Node) (term : Term Symbol) :
    Forest ops (reduceClass ops paths nodes) term → Forest ops nodes term :=
  laws.edit_narrow _ _ _

/-- Every valid class term survives the complete simultaneous class edit. -/
theorem reduceClass_keep (ops : Operations Node Symbol) (laws : Laws ops)
    (paths : Class) (active : Nontrivial paths) (nonroot : ∀ path ∈ paths, path ≠ [])
    (nodes : List Node) (term : Term Symbol) (accepted : Forest ops nodes term) (satisfied : ClassSat term paths) :
    Forest ops (reduceClass ops paths nodes) term := by
  apply laws.edit_keep _ nodes term accepted
  intro path target member subtree found
  obtain ⟨selected, present, equal⟩ := List.mem_map.mp member
  have pathSame : selected = path := congrArg Prod.fst equal
  subst selected
  have targetSame := congrArg Prod.snd equal
  dsimp only at targetSame
  rw [← targetSame]
  apply (intersectList_exact ops laws _ (by simpa using EqualityNarrowing.others_nonempty paths active path) subtree).mpr
  intro projected projectedMember
  obtain ⟨other, otherPresent, rfl⟩ := List.mem_map.mp projectedMember
  have otherMember : other ∈ paths := (List.mem_filter.mp otherPresent).1
  obtain ⟨value, pathValue, otherValue⟩ := class_pair_equal term paths active satisfied path other present otherMember
  have same : value = subtree := Option.some.inj (pathValue.symm.trans found)
  subst value
  exact laws.project nodes term other subtree (nonroot other otherMember) accepted otherValue

/-- Retain every class whose paths do not cross a blocked recursive node. -/
def selectedClasses (ops : Operations Node Symbol) (localClasses : Constraints) (nodes : List Node) : Constraints :=
  localClasses.filter (fun paths => !(ops.blocked nodes paths))

/-- Source empty-child propagation uses structural identity, not solver rejection. -/
def propagate [DecidableEq Node] (ops : Operations Node Symbol) (nodes : List Node) : List Node :=
  if ops.empty ∈ nodes then nodes.map (fun _ => ops.empty) else nodes

/-- Empty-child propagation preserves the whole forest language. -/
theorem propagate_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (nodes : List Node) (term : Term Symbol) : Forest ops (propagate ops nodes) term ↔ Forest ops nodes term := by
  by_cases hasEmpty : ops.empty ∈ nodes
  · cases term with
    | node symbol children =>
      have before : ¬ All₂ ops.meaning nodes children := by
        intro runs
        obtain ⟨value, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ runs ops.empty hasEmpty
        exact laws.empty value accepted
      have after : ¬ All₂ ops.meaning (nodes.map fun _ => ops.empty) children := by
        intro runs
        have present : ops.empty ∈ nodes.map (fun _ => ops.empty) := List.mem_map.mpr ⟨ops.empty, hasEmpty, rfl⟩
        obtain ⟨value, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ runs ops.empty present
        exact laws.empty value accepted
      simp [Forest, propagate, hasEmpty, before, after]
  · simp [propagate, hasEmpty]

/-- The exact source class selection, required-path union, right fold and empty propagation. -/
def pass [DecidableEq Node] (ops : Operations Node Symbol) (localClasses inherited : Constraints) (nodes : List Node) : List Node :=
  if localClasses = [] ∧ inherited = [] then nodes
  else if ops.contradictory localClasses inherited then nodes.map (fun _ => ops.empty)
  else
    let selected := selectedClasses ops localClasses nodes
    propagate ops (selected.foldr (reduceClass ops) (ops.requireAll selected.flatten nodes))

/-- A right fold of class reductions cannot introduce a new forest term. -/
theorem classes_narrow (ops : Operations Node Symbol) (laws : Laws ops) (classes : Constraints)
    (nodes : List Node) (term : Term Symbol) :
    Forest ops (classes.foldr (reduceClass ops) nodes) term → Forest ops nodes term := by
  induction classes with
  | nil => exact id
  | cons paths rest ih => exact fun accepted => ih (reduceClass_narrow ops laws paths _ term accepted)

/-- Every class in the selected pass preserves a globally valid original term. -/
theorem classes_keep (ops : Operations Node Symbol) (laws : Laws ops) (classes : Constraints)
    (active : Active classes) (nonroot : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (nodes : List Node) (term : Term Symbol) (accepted : Forest ops nodes term) (satisfied : Satisfies term classes) :
    Forest ops (classes.foldr (reduceClass ops) nodes) term := by
  induction classes with
  | nil => exact accepted
  | cons paths rest ih =>
    apply reduceClass_keep ops laws paths (active paths (by simp)) (nonroot paths (by simp)) _ term
    · exact ih (fun paths member => active paths (by simp [member]))
        (fun paths member => nonroot paths (by simp [member])) (fun paths member => satisfied paths (by simp [member]))
    · exact satisfied paths (by simp)

/-- One full source pass preserves every term satisfying the local and inherited classes. -/
theorem pass_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (localClasses inherited : Constraints) (active : Active localClasses)
    (nonroot : ∀ paths ∈ localClasses, ∀ path ∈ paths, path ≠ []) (nodes : List Node) (term : Term Symbol)
    (satisfied : Satisfies term localClasses ∧ Satisfies term inherited) :
    Forest ops (pass ops localClasses inherited nodes) term ↔ Forest ops nodes term := by
  unfold pass
  split
  · rfl
  · have consistent : ops.contradictory localClasses inherited = false := by
      cases found : ops.contradictory localClasses inherited with
      | false => rfl
      | true => exact False.elim (laws.contradiction localClasses inherited term found satisfied)
    simp only [consistent, Bool.false_eq_true, ite_false]
    rw [propagate_exact ops laws]
    have subset : ∀ paths ∈ selectedClasses ops localClasses nodes, paths ∈ localClasses := fun _ member => (List.mem_filter.mp member).1
    have selectedActive : Active (selectedClasses ops localClasses nodes) := fun paths member => active paths (subset paths member)
    have selectedSatisfied : Satisfies term (selectedClasses ops localClasses nodes) := fun paths member => satisfied.1 paths (subset paths member)
    constructor
    · intro accepted
      exact laws.require_narrow _ nodes term (classes_narrow ops laws _ _ term accepted)
    · intro accepted
      apply classes_keep ops laws _ selectedActive
        (fun paths member => nonroot paths (subset paths member)) _ term _ selectedSatisfied
      apply laws.require_keep _ nodes term accepted
      intro path member
      obtain ⟨paths, pathsMember, pathMember⟩ := List.mem_flatten.mp member
      exact class_member_exists term paths (selectedActive paths pathsMember)
        (selectedSatisfied paths pathsMember) path pathMember

/-- Bounded instrumentation of the source identity-based fixed point. -/
def reduce [DecidableEq Node] (ops : Operations Node Symbol) (localClasses inherited : Constraints) : Nat → List Node → Option (List Node)
  | 0, _ => none
  | fuel + 1, nodes =>
    let next := pass ops localClasses inherited nodes
    if next = nodes then some nodes else reduce ops localClasses inherited fuel next

/-- Every completed repeated reduction preserves exactly the constrained forest terms. -/
theorem reduce_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (localClasses inherited : Constraints) (active : Active localClasses)
    (nonroot : ∀ paths ∈ localClasses, ∀ path ∈ paths, path ≠ []) (fuel : Nat) (before after : List Node)
    (completed : reduce ops localClasses inherited fuel before = some after) (term : Term Symbol)
    (satisfied : Satisfies term localClasses ∧ Satisfies term inherited) :
    Forest ops after term ↔ Forest ops before term := by
  induction fuel generalizing before with
  | zero => simp [reduce] at completed
  | succ fuel ih =>
    simp only [reduce] at completed
    split at completed
    · cases completed; rfl
    · exact (ih _ completed).trans (pass_exact ops laws localClasses inherited active nonroot before term satisfied)

/-- A nontrivial satisfiable finite-tree class cannot contain the root path. -/
theorem class_nonroot (paths : Class) (active : Nontrivial paths) (term : Term Symbol)
    (satisfied : ClassSat term paths) : ∀ path ∈ paths, path ≠ [] := by
  intro path member same
  subst path
  obtain ⟨left, leftMember, right, rightMember, different⟩ := active
  have noOther : ∀ other ∈ paths, other = [] := by
    intro other present
    apply Classical.byContradiction
    intro nonempty
    have equal := class_pair_equal term paths ⟨left, leftMember, right, rightMember, different⟩
      satisfied [] other member present
    exact strict_prefix_paths_not_equal term [] other nonempty (by simpa using equal)
  exact different ((noOther left leftMember).trans (noOther right rightMember).symm)

/-- The completed loop preserves the exact language under both original constraint sets. -/
theorem constrained_reduce_exact [DecidableEq Node] (ops : Operations Node Symbol) (laws : Laws ops)
    (localClasses inherited : Constraints) (active : Active localClasses) (fuel : Nat) (before after : List Node)
    (completed : reduce ops localClasses inherited fuel before = some after) (term : Term Symbol) :
    (Forest ops after term ∧ Satisfies term localClasses ∧ Satisfies term inherited) ↔
      Forest ops before term ∧ Satisfies term localClasses ∧ Satisfies term inherited := by
  constructor
  · rintro ⟨accepted, localSat, inheritedSat⟩
    have exact := reduce_exact ops laws localClasses inherited active
      (fun paths member => class_nonroot paths (active paths member) term (localSat paths member))
      fuel before after completed term ⟨localSat, inheritedSat⟩
    exact ⟨exact.mp accepted, localSat, inheritedSat⟩
  · rintro ⟨accepted, localSat, inheritedSat⟩
    have exact := reduce_exact ops laws localClasses inherited active
      (fun paths member => class_nonroot paths (active paths member) term (localSat paths member))
      fuel before after completed term ⟨localSat, inheritedSat⟩
    exact ⟨exact.mpr accepted, localSat, inheritedSat⟩

end MicroCFTA.EqualityReduction
