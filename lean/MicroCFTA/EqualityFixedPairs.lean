import Std

/-!
# Fixed equality schedules with disjoint binary child classes

Each binary class reads both child roots from one input forest and replaces
both roots with the same intersection. A fixed schedule of disjoint pairs
therefore reaches a structural fixed point after one pass. Empty propagation
preserves that result. The node domain may contain arbitrarily nested closed
nodes. Only commutativity and the source self-intersection law are used.
The theorem does not cover path projections that union several occurrences.
-/
namespace MicroCFTA.EqualityFixedPairs

/-- Two direct child positions form one binary equality class. -/
abbrev Pair (Index : Type) := Index × Index

/-- A forest records the node identity at each fixed child position. -/
abbrev Forest (Index Node : Type) := Index → Node

/-- Two classes edit disjoint child positions. -/
def Disjoint (first second : Pair Index) : Prop :=
  first.1 ≠ second.1 ∧ first.1 ≠ second.2 ∧ first.2 ≠ second.1 ∧ first.2 ≠ second.2

/-- Disjointness of equality classes is symmetric. -/
theorem disjoint_symm (first second : Pair Index) (disjoint : Disjoint first second) : Disjoint second first :=
  ⟨Ne.symm disjoint.1, Ne.symm disjoint.2.2.1, Ne.symm disjoint.2.1, Ne.symm disjoint.2.2.2⟩

/-- The source edits one child while retaining all other positions. -/
def edit [DecidableEq Index] (index : Index) (change : Node → Node) (forest : Forest Index Node) : Forest Index Node :=
  fun other => if other = index then change (forest other) else forest other

/-- The source right fold computes both binary-class targets from the unchanged input forest. -/
def sourcePair [DecidableEq Index] (meet : Node → Node → Node) (pair : Pair Index)
    (forest : Forest Index Node) : Forest Index Node :=
  edit pair.1 (meet (forest pair.2)) (edit pair.2 (meet (forest pair.1)) forest)

/-- A symmetric binary class stores one common node at both endpoints. -/
def narrow [DecidableEq Index] (meet : Node → Node → Node) (pair : Pair Index)
    (forest : Forest Index Node) : Forest Index Node :=
  fun index => if index = pair.1 ∨ index = pair.2 then meet (forest pair.1) (forest pair.2) else forest index

/-- Snapshot targets and disjoint root edits produce exactly the symmetric class update. -/
theorem sourcePair_exact [DecidableEq Index] (meet : Node → Node → Node)
    (comm : ∀ left right, meet left right = meet right left) (pair : Pair Index) (distinct : pair.1 ≠ pair.2)
    (forest : Forest Index Node) : sourcePair meet pair forest = narrow meet pair forest := by
  funext index
  by_cases left : index = pair.1 <;> by_cases right : index = pair.2
  all_goals simp_all [sourcePair, edit, narrow]

/-- Both endpoint projections are the same node identity after the binary update. -/
theorem equal_after [DecidableEq Index] (meet : Node → Node → Node) (pair : Pair Index) (forest : Forest Index Node) :
    narrow meet pair forest pair.1 = narrow meet pair forest pair.2 := by
  simp [narrow]

/-- Self-intersection makes a repeated binary-class pass structurally idempotent. -/
theorem narrow_fixed [DecidableEq Index] (meet : Node → Node → Node) (idem : ∀ node, meet node node = node)
    (pair : Pair Index) (forest : Forest Index Node) : narrow meet pair (narrow meet pair forest) = narrow meet pair forest := by
  funext index
  by_cases selected : index = pair.1 ∨ index = pair.2 <;> simp [narrow, selected, idem]

/-- Edits from another disjoint class do not change either input projection. -/
theorem endpoints_unchanged [DecidableEq Index] (meet : Node → Node → Node) (first second : Pair Index)
    (disjoint : Disjoint first second) (forest : Forest Index Node) :
    narrow meet second forest first.1 = forest first.1 ∧ narrow meet second forest first.2 = forest first.2 := by
  simp [narrow, disjoint.1, disjoint.2.1, disjoint.2.2.1, disjoint.2.2.2]

/-- Disjoint symmetric class updates commute, without associativity of node intersection. -/
theorem narrow_commute [DecidableEq Index] (meet : Node → Node → Node) (first second : Pair Index)
    (disjoint : Disjoint first second) (forest : Forest Index Node) :
    narrow meet first (narrow meet second forest) = narrow meet second (narrow meet first forest) := by
  have symmetric := disjoint_symm first second disjoint
  funext index
  simp only [narrow, disjoint.1, disjoint.2.1, disjoint.2.2.1, disjoint.2.2.2,
    symmetric.1, symmetric.2.1, symmetric.2.2.1, symmetric.2.2.2, or_self, ↓reduceIte]
  by_cases a : index = first.1 ∨ index = first.2 <;> by_cases b : index = second.1 ∨ index = second.2
  all_goals simp only [a, b, ↓reduceIte]
  rcases a with rfl | rfl <;> rcases b with same | same
  · exact False.elim (disjoint.1 same)
  · exact False.elim (disjoint.2.1 same)
  · exact False.elim (disjoint.2.2.1 same)
  · exact False.elim (disjoint.2.2.2 same)

/-- A fixed equality schedule uses the same right-fold order as the source. -/
def pass [DecidableEq Index] (meet : Node → Node → Node) (pairs : List (Pair Index)) (forest : Forest Index Node) : Forest Index Node :=
  pairs.foldr (narrow meet) forest

/-- A disjoint binary update commutes with the complete remaining schedule. -/
theorem pass_commute [DecidableEq Index] (meet : Node → Node → Node) (pair : Pair Index) (pairs : List (Pair Index))
    (disjoint : ∀ other ∈ pairs, Disjoint pair other) (forest : Forest Index Node) :
    pass meet pairs (narrow meet pair forest) = narrow meet pair (pass meet pairs forest) := by
  induction pairs with
  | nil => rfl
  | cons first rest ih =>
      simp only [pass, List.foldr_cons]
      rw [show rest.foldr (narrow meet) (narrow meet pair forest) = narrow meet pair (rest.foldr (narrow meet) forest) from
        ih (fun other member => disjoint other (by simp [member]))]
      exact (narrow_commute meet pair first (disjoint first (by simp)) _).symm

/-- A fixed schedule of disjoint binary direct-child classes is idempotent for nested node domains. -/
theorem pass_fixed [DecidableEq Index] (meet : Node → Node → Node) (idem : ∀ node, meet node node = node)
    (pairs : List (Pair Index)) (separate : pairs.Pairwise Disjoint) (forest : Forest Index Node) :
    pass meet pairs (pass meet pairs forest) = pass meet pairs forest := by
  induction pairs with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨apart, inside⟩ := List.pairwise_cons.mp separate
      change narrow meet first (pass meet rest (narrow meet first (pass meet rest forest))) = narrow meet first (pass meet rest forest)
      rw [pass_commute meet first rest apart, narrow_fixed meet idem, ih inside]

/-- The source restores one shared empty node at all child positions after any empty result. -/
noncomputable def propagate (empty : Node) (forest : Forest Index Node) : Forest Index Node := by
  classical
  exact if ∃ index, forest index = empty then fun _ => empty else forest

/-- The all-empty forest is a structural fixed point of propagation. -/
theorem propagate_empty (empty : Node) : propagate empty (fun (_ : Index) => empty) = fun _ => empty := by
  classical
  unfold propagate
  split <;> rfl

/-- Every binary class leaves the all-empty forest unchanged by self-intersection. -/
theorem pass_empty [DecidableEq Index] (meet : Node → Node → Node) (idem : ∀ node, meet node node = node)
    (empty : Node) (pairs : List (Pair Index)) : pass meet pairs (fun _ => empty) = fun _ => empty := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      change narrow meet pair (pass meet rest (fun _ => empty)) = _
      rw [ih]
      funext index
      simp [narrow, idem]

/-- The completed direct-child pass includes the actual empty-propagation phase. -/
noncomputable def round [DecidableEq Index] (meet : Node → Node → Node) (empty : Node)
    (pairs : List (Pair Index)) (forest : Forest Index Node) : Forest Index Node := propagate empty (pass meet pairs forest)

/-- Empty propagation cannot introduce a second structural change in this fixed schedule. -/
theorem round_fixed [DecidableEq Index] (meet : Node → Node → Node) (idem : ∀ node, meet node node = node)
    (empty : Node) (pairs : List (Pair Index)) (separate : pairs.Pairwise Disjoint) (forest : Forest Index Node) :
    round meet empty pairs (round meet empty pairs forest) = round meet empty pairs forest := by
  classical
  by_cases hasEmpty : ∃ index, pass meet pairs forest index = empty
  · have propagated : round meet empty pairs forest = fun _ => empty := by simp [round, propagate, hasEmpty]
    rw [propagated]
    exact (congrArg (propagate empty) (pass_empty meet idem empty pairs)).trans (propagate_empty empty)
  · have unchanged : round meet empty pairs forest = pass meet pairs forest := by simp [round, propagate, hasEmpty]
    rw [unchanged]
    change propagate empty (pass meet pairs (pass meet pairs forest)) = pass meet pairs forest
    rw [pass_fixed meet idem pairs separate]
    simp [propagate, hasEmpty]

/-- The source identity fixed point with explicit proof fuel. -/
noncomputable def run [DecidableEq Index] (meet : Node → Node → Node) (empty : Node) (pairs : List (Pair Index)) :
    Nat → Forest Index Node → Option (Forest Index Node)
  | 0, _ => none
  | fuel + 1, forest => by
      classical
      exact let next := round meet empty pairs forest
        if next = forest then some forest else run meet empty pairs fuel next

/-- Two tests suffice: the one possible changing pass and the following identity test. -/
theorem run_two [DecidableEq Index] (meet : Node → Node → Node) (idem : ∀ node, meet node node = node)
    (empty : Node) (pairs : List (Pair Index)) (separate : pairs.Pairwise Disjoint) (forest : Forest Index Node) :
    run meet empty pairs 2 forest = some (round meet empty pairs forest) := by
  classical
  by_cases fixed : round meet empty pairs forest = forest
  · simp [run, fixed]
  · simp [run, fixed, round_fixed meet idem empty pairs separate forest]

/-- Apply the actual binary snapshot edits in the fixed source right-fold order. -/
def sourcePass [DecidableEq Index] (meet : Node → Node → Node) (pairs : List (Pair Index))
    (forest : Forest Index Node) : Forest Index Node := pairs.foldr (sourcePair meet) forest

/-- Distinct binary endpoints connect the source snapshot schedule to symmetric narrowing. -/
theorem sourcePass_exact [DecidableEq Index] (meet : Node → Node → Node)
    (comm : ∀ left right, meet left right = meet right left) (pairs : List (Pair Index))
    (distinct : ∀ pair ∈ pairs, pair.1 ≠ pair.2) (forest : Forest Index Node) :
    sourcePass meet pairs forest = pass meet pairs forest := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [sourcePass, pass, List.foldr_cons]
      rw [sourcePair_exact meet comm pair (distinct pair (by simp))]
      exact congrArg (narrow meet pair) (ih (fun pair member => distinct pair (by simp [member])))

/-- The source snapshot pass plus empty propagation reaches the same fixed forest after one pass. -/
theorem source_round_fixed [DecidableEq Index] (meet : Node → Node → Node)
    (comm : ∀ left right, meet left right = meet right left) (idem : ∀ node, meet node node = node)
    (empty : Node) (pairs : List (Pair Index)) (distinct : ∀ pair ∈ pairs, pair.1 ≠ pair.2)
    (separate : pairs.Pairwise Disjoint) (forest : Forest Index Node) :
    propagate empty (sourcePass meet pairs (propagate empty (sourcePass meet pairs forest))) =
      propagate empty (sourcePass meet pairs forest) := by
  simp only [sourcePass_exact meet comm pairs distinct]
  exact round_fixed meet idem empty pairs separate forest

end MicroCFTA.EqualityFixedPairs
