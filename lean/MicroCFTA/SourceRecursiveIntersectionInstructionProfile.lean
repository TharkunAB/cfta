import MicroCFTA.SourceRecursiveIntersectionSourceProfile

/-!
# Initial branching limits and instruction credit

The source payload inventory bounds literal row pairs, union members, and
ordered child pairs. The credit recurrence uses only this fixed source limit
and a supplied semantic rank. It does not assert an execution length.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInstructionProfile
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedEdgeResidency SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
variable {Symbol Guard : Type}

/-- One limit bounds every literal request-list width in the source. -/
def branching (bounds : SourceRecursiveIntersectionSourceProfile.Limits) : Nat :=
  max 1 (max (bounds.rows * bounds.rows) (max bounds.members bounds.arity))

/-- Compute the request-list limit from the initial source payload inventory. -/
def sourceBranching (source : State Symbol Guard) : Nat :=
  branching (SourceRecursiveIntersectionSourceProfile.limits source)

/-- Reserve four local instructions and one smaller credit for each branch. -/
def budget (limit : Nat) : Nat → Nat
  | 0 => 0
  | height + 1 => 4 + limit * budget limit height

/-- Rank zero has no instruction credit. -/
theorem budget_zero (limit : Nat) : budget limit 0 = 0 := rfl

/-- A successor rank has the literal recursive credit. -/
theorem budget_succ (limit height : Nat) :
    budget limit (height + 1) = 4 + limit * budget limit height := rfl

/-- A successor rank never decreases the instruction credit. -/
theorem budget_succ_ge (limit height : Nat) : budget limit height ≤ budget limit (height + 1) := by
  induction height with
  | zero => exact Nat.zero_le _
  | succ height ih =>
      exact Nat.add_le_add_left (Nat.mul_le_mul_left limit ih) 4

/-- A larger branching limit retains the same rank credit. -/
theorem budget_mono {first last : Nat} (increase : first ≤ last) (height : Nat) :
    budget first height ≤ budget last height := by
  induction height with
  | zero => exact Nat.le_refl _
  | succ height ih => exact Nat.add_le_add_left (Nat.mul_le_mul increase ih) 4

/-- A larger semantic rank retains the same branching credit. -/
theorem budget_height_mono (limit : Nat) {first last : Nat} (increase : first ≤ last) :
    budget limit first ≤ budget limit last := by
  induction increase with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (budget_succ_ge limit last)

/-- Increasing both initial parameters retains the instruction credit. -/
theorem budget_parameters_mono {firstLimit lastLimit firstHeight lastHeight : Nat}
    (limits : firstLimit ≤ lastLimit) (heights : firstHeight ≤ lastHeight) :
    budget firstLimit firstHeight ≤ budget lastLimit lastHeight :=
  Nat.le_trans (budget_mono limits firstHeight) (budget_height_mono lastLimit heights)

/-- Every positive semantic rank reserves at least four instructions. -/
theorem budget_ge_four (limit height : Nat) (positive : 0 < height) : 4 ≤ budget limit height := by
  cases height with
  | zero => omega
  | succ height => simp only [budget]; omega

/-- Every positive semantic rank has positive instruction credit. -/
theorem budget_pos (limit height : Nat) (positive : 0 < height) : 0 < budget limit height :=
  Nat.lt_of_lt_of_le (by omega) (budget_ge_four limit height positive)

/-- The source limit always includes one branch. -/
theorem branching_pos (bounds : SourceRecursiveIntersectionSourceProfile.Limits) :
    1 ≤ branching bounds := Nat.le_max_left _ _

/-- The source limit includes every ordered row occurrence pair. -/
theorem branching_rows (bounds : SourceRecursiveIntersectionSourceProfile.Limits) :
    bounds.rows * bounds.rows ≤ branching bounds :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The source limit includes every literal union member. -/
theorem branching_members (bounds : SourceRecursiveIntersectionSourceProfile.Limits) :
    bounds.members ≤ branching bounds :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- The source limit includes every literal ordered child. -/
theorem branching_arity (bounds : SourceRecursiveIntersectionSourceProfile.Limits) :
    bounds.arity ≤ branching bounds :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- The computed initial source limit is at least one. -/
theorem sourceBranching_pos (source : State Symbol Guard) : 1 ≤ sourceBranching source :=
  branching_pos _

private theorem pairs_length_le [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard)) :
    (SourceRecursiveIntersectionKernel.pairs left right).length ≤ left.length * right.length := by
  rw [SourceRecursiveIntersectionKernel.pairs, SymbolicHashJoin.hashJoin_length]
  induction left with
  | nil => simp
  | cons first rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have bounded := Nat.add_le_add
        (List.length_filter_le (fun second => decide (first.entry.key.symbol = second.entry.key.symbol)) right) ih
      omega

/-- Actual source node scope bounds the literal equal-symbol row join. -/
theorem row_pairs [DecidableEq Symbol] (source : State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) :
    (SourceRecursiveIntersectionKernel.pairs (nodeEdges request.left) (nodeEdges request.right)).length ≤
      sourceBranching source := by
  have shapes := SourceRecursiveIntersectionSourceProfile.node_scope source facts request scope
  exact Nat.le_trans (pairs_length_le _ _) (Nat.le_trans (Nat.mul_le_mul shapes.1.1 shapes.2.1)
    (branching_rows _))

/-- Actual source node scope bounds the left literal union member list. -/
theorem left_members (source : State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) :
    SourceRecursiveIntersectionSourceProfile.memberCount request.left ≤ sourceBranching source :=
  Nat.le_trans (SourceRecursiveIntersectionSourceProfile.node_scope source facts request scope).1.2
    (branching_members _)

/-- Actual source node scope bounds the right literal union member list. -/
theorem right_members (source : State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) :
    SourceRecursiveIntersectionSourceProfile.memberCount request.right ≤ sourceBranching source :=
  Nat.le_trans (SourceRecursiveIntersectionSourceProfile.node_scope source facts request scope).2.2
    (branching_members _)

/-- Actual source edge scope bounds the ordered zipped child requests. -/
theorem edge_zip (source : State Symbol Guard) (facts : Facts source)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request) :
    (request.left.children.zip request.right.children).length ≤ sourceBranching source := by
  have shapes := SourceRecursiveIntersectionSourceProfile.edge_scope source facts request scope
  exact Nat.le_trans (by rw [List.length_zip]; exact Nat.min_le_left _ _)
    (Nat.le_trans shapes.1 (branching_arity _))

end MicroCFTA.SourceRecursiveIntersectionInstructionProfile
