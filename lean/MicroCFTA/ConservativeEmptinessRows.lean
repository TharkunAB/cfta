import MicroCFTA.ConservativeEmptiness
import MicroCFTA.EqualityReduction

/-!
# Smaller witnesses for source-shaped emptiness rows

A row retains its original children and one intersection for each equality
class. Class intersections use `foldr1` order. They do not use the different
seeded fold in the equality reduction pass. Projection and intersection laws
derive smaller witnesses from an accepted forest and satisfied classes.
Physical classification and one-level node exposure remain explicit premises.
The source exploration and its cache effects are not modeled here.
-/
namespace MicroCFTA.ConservativeEmptinessRows
open Language EqualityNormalize EqualityReduction ConservativeEmptiness

variable {Node Symbol State : Type}

/-- Only empty, intersection, and projection semantics are needed by emptiness rows. -/
structure PrimitiveLaws (ops : Operations Node Symbol) : Prop where
  empty : ∀ term, ¬ops.meaning ops.empty term
  intersect : ∀ left right term,
    ops.meaning (ops.intersect left right) term ↔ ops.meaning left term ∧ ops.meaning right term
  project : ∀ children term path subtree, path ≠ [] → Forest ops children term →
    term.atPath path = some subtree → ops.meaning (ops.project children path) subtree

/-- Existing equality-reduction laws supply these three primitive contracts. -/
theorem PrimitiveLaws.ofReduction (ops : Operations Node Symbol) (laws : EqualityReduction.Laws ops) : PrimitiveLaws ops :=
  ⟨laws.empty, laws.intersect, laws.project⟩

/-- Intersect a nonempty list in source `foldr1` order, with empty as a total fallback. -/
def foldr1Intersection (ops : Operations Node Symbol) : List Node → Node
  | [] => ops.empty
  | [node] => node
  | node :: next :: rest => ops.intersect node (foldr1Intersection ops (next :: rest))

/-- The source `foldr1` retains exactly the terms common to every listed node. -/
theorem foldr1_exact (ops : Operations Node Symbol) (laws : PrimitiveLaws ops)
    (nodes : List Node) (nonempty : nodes ≠ []) (term : Term Symbol) :
    ops.meaning (foldr1Intersection ops nodes) term ↔ ∀ node ∈ nodes, ops.meaning node term := by
  induction nodes with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest ih =>
      cases rest with
      | nil => simp [foldr1Intersection]
      | cons next rest =>
          rw [foldr1Intersection, laws.intersect, ih (by simp)]
          simp

/-- One class requirement reads all paths from the same original child list. -/
def classIntersection (ops : Operations Node Symbol) (children : List Node) (paths : Class) : Node :=
  foldr1Intersection ops (paths.map (ops.project children))

/-- An exposed edge contributes its original child list and normalized classes. -/
structure Row (Node : Type) where
  children : List Node
  classes : Constraints

/-- The source row appends one shared-subterm intersection for each class. -/
def requirements (ops : Operations Node Symbol) (row : Row Node) : List Node :=
  row.children ++ row.classes.map (classIntersection ops row.children)

/-- A satisfied nontrivial class supplies an accepted proper subterm in its intersection. -/
theorem class_witness (ops : Operations Node Symbol) (laws : PrimitiveLaws ops) (children : List Node)
    (paths : Class) (active : Nontrivial paths) (term : Term Symbol)
    (forest : Forest ops children term) (satisfied : ClassSat term paths) :
    ∃ subtree, ops.meaning (classIntersection ops children paths) subtree ∧ subtree.height < term.height := by
  obtain ⟨first, firstMember, other, otherMember, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstMember, other, otherMember, different⟩
  obtain ⟨subtree, found⟩ := class_member_exists term paths active satisfied first firstMember
  have nonroot := class_nonroot paths active term satisfied
  have nonempty : paths ≠ [] := by intro empty; subst paths; cases firstMember
  refine ⟨subtree, ?_, ?_⟩
  · apply (foldr1_exact ops laws _ (by simpa using nonempty) subtree).mpr
    intro projected member
    obtain ⟨path, pathMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨common, firstFound, pathFound⟩ := class_pair_equal term paths active satisfied first path firstMember pathMember
    have same : common = subtree := Option.some.inj (firstFound.symm.trans found)
    subst common
    exact laws.project children term path subtree (nonroot path pathMember) forest pathFound
  · have bound := atPath_height_bound term subtree first found
    have positive : 0 < first.length := by
      cases first with
      | nil => exact False.elim (nonroot [] firstMember rfl)
      | cons index rest => simp
    omega

/-- Every original child of an accepted forest has a smaller accepted witness. -/
theorem child_witness (ops : Operations Node Symbol) (children : List Node) (term : Term Symbol)
    (forest : Forest ops children term) (child : Node) (member : child ∈ children) :
    ∃ subtree, ops.meaning child subtree ∧ subtree.height < term.height := by
  cases term with
  | node symbol terms =>
      obtain ⟨subtree, selected, accepted⟩ := SymbolicSmartRows.all₂_child ops.meaning children terms forest child member
      refine ⟨subtree, accepted, ?_⟩
      have bound := height_le_forestHeight terms subtree selected
      simpa only [Term.height, forestHeight] using Nat.lt_succ_of_le bound

/-- Every requirement of an accepted source-shaped row has a smaller accepted witness. -/
theorem row_witness (ops : Operations Node Symbol) (laws : PrimitiveLaws ops) (row : Row Node)
    (active : Active row.classes) (term : Term Symbol) (forest : Forest ops row.children term)
    (satisfied : Satisfies term row.classes) :
    ∀ node ∈ requirements ops row, ∃ subtree, ops.meaning node subtree ∧ subtree.height < term.height := by
  intro node member
  rcases List.mem_append.mp member with child | intersection
  · exact child_witness ops row.children term forest node child
  · obtain ⟨paths, classMember, rfl⟩ := List.mem_map.mp intersection
    exact class_witness ops laws row.children paths (active paths classMember) term forest (satisfied paths classMember)

/-- Inside keys read back the same original node; empty keys identify the primitive empty node. -/
def Readback (ops : Operations Node Symbol) (read : State → Node) (classify : Node → Requirement State) : Prop :=
  ∀ node, match classify node with
    | .empty => node = ops.empty
    | .outside => True
    | .inside state => node = read state

/-- A smaller semantic witness remains a valid obligation after physical classification. -/
theorem classified_obligation (ops : Operations Node Symbol) (laws : PrimitiveLaws ops)
    (read : State → Node) (classify : Node → Requirement State) (readback : Readback ops read classify)
    (parent subtree : Term Symbol) (node : Node) (accepted : ops.meaning node subtree)
    (smaller : subtree.height < parent.height) :
    Obligation (fun state => ops.meaning (read state)) Term.height parent (classify node) := by
  have identity := readback node
  cases classified : classify node with
  | empty =>
      simp only [classified] at identity
      exact laws.empty subtree (identity ▸ accepted)
  | outside => trivial
  | inside state =>
      simp only [classified] at identity
      exact ⟨subtree, by simpa only [identity] using accepted, smaller⟩

/-- Classify the actual original requirements of each exposed row. -/
def graphRows (ops : Operations Node Symbol) (classify : Node → Requirement State)
    (exposed : State → List (Row Node)) (state : State) : List (List (Requirement State)) :=
  (exposed state).map (fun row => (requirements ops row).map classify)

/-- Accepted node readback exposes one original edge with its children and satisfied active classes. -/
def Exposure (ops : Operations Node Symbol) (read : State → Node) (exposed : State → List (Row Node)) : Prop :=
  ∀ state term, ops.meaning (read state) term →
    ∃ row ∈ exposed state, Forest ops row.children term ∧ Satisfies term row.classes ∧ Active row.classes

/-- Primitive graph laws and local node exposure derive the algorithm's semantic decomposition premise. -/
theorem decomposes (ops : Operations Node Symbol) (laws : PrimitiveLaws ops)
    (read : State → Node) (classify : Node → Requirement State) (readback : Readback ops read classify)
    (exposed : State → List (Row Node)) (exposure : Exposure ops read exposed) :
    Decomposes (graphRows ops classify exposed) (fun state => ops.meaning (read state)) Term.height := by
  intro state term accepted
  obtain ⟨row, member, forest, satisfied, active⟩ := exposure state term accepted
  refine ⟨(requirements ops row).map classify, List.mem_map.mpr ⟨row, member, rfl⟩, ?_⟩
  intro requirement selected
  obtain ⟨node, member, rfl⟩ := List.mem_map.mp selected
  obtain ⟨subtree, witness, smaller⟩ := row_witness ops laws row active term forest satisfied node member
  exact classified_obligation ops laws read classify readback term subtree node witness smaller

/-- Source-shaped finite rows reject no term when primitive readback and one-level exposure hold. -/
theorem provablyEmpty_sound (states : List State) (complete : ∀ state, state ∈ states)
    (ops : Operations Node Symbol) (laws : PrimitiveLaws ops) (read : State → Node)
    (classify : Node → Requirement State) (readback : Readback ops read classify)
    (exposed : State → List (Row Node)) (exposure : Exposure ops read exposed) (query : Requirement State)
    (empty : ConservativeEmptiness.provablyEmpty states (graphRows ops classify exposed) query = true) :
    ∀ term, ¬AcceptsRequirement (fun state => ops.meaning (read state)) query term :=
  ConservativeEmptiness.provablyEmpty_sound states complete _ _ Term.height
    (decomposes ops laws read classify readback exposed exposure) query empty

end MicroCFTA.ConservativeEmptinessRows
