import MicroCFTA.SourceLeafRowProgress

/-!
# Structural progress of complete leaf-forest equality schedules

Each class reads all projections from the same input forest. It narrows
every selected direct child to the intersection of the other projections.
The source right fold can change classes between passes. The proof sums
finite leaf potentials and keeps the exact whole-node self shortcut.
-/
namespace MicroCFTA.FiniteLeafForestProgress
open FiniteRowIntersection

/-- Encode the bounded lexicographic leaf measure as one natural number. -/
noncomputable def potential (algebra : Conjunction Row) (inventory : List Row) (rows : Rows Row) : Nat :=
  (measure algebra inventory rows).1 * (inventory.length + 1) + (measure algebra inventory rows).2

/-- Every changing leaf intersection strictly decreases its natural potential. -/
theorem intersect_strict (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (left right : Rows Row) (changed : intersect algebra left right ≠ left) :
    potential algebra inventory (intersect algebra left right) < potential algebra inventory left := by
  have progress := intersect_progress algebra inventory complete left right changed
  have lastBound : (measure algebra inventory (intersect algebra left right)).2 ≤ inventory.length := Nat.sub_le _ _
  rcases Prod.lex_def.mp progress with smaller | ⟨equal, smaller⟩
  ·
      have multiplied := Nat.mul_le_mul_right (inventory.length + 1) (Nat.succ_le_of_lt smaller)
      simp only [potential]
      rw [Nat.succ_mul] at multiplied
      omega
  ·
      simp only [potential]
      rw [equal]
      omega

/-- A local operation preserves the row set or strictly decreases its potential. -/
def Improves (algebra : Conjunction Row) (inventory : List Row) (after before : Rows Row) : Prop :=
  after = before ∨ potential algebra inventory after < potential algebra inventory before

/-- Equality is a valid unchanged step. -/
theorem improves_refl (algebra : Conjunction Row) (inventory : List Row) (rows : Rows Row) :
    Improves algebra inventory rows rows := Or.inl rfl

/-- Local progress composes through every sequential source edit. -/
theorem improves_trans (algebra : Conjunction Row) (inventory : List Row) (first middle last : Rows Row)
    (left : Improves algebra inventory middle first) (right : Improves algebra inventory last middle) :
    Improves algebra inventory last first := by
  rcases left with rfl | left
  · exact right
  · rcases right with rfl | right
    · exact Or.inr left
    · exact Or.inr (Nat.lt_trans right left)

/-- Leaf intersection supplies progress without assuming absorption. -/
theorem intersect_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (left right : Rows Row) : Improves algebra inventory (intersect algebra left right) left := by
  classical
  by_cases same : intersect algebra left right = left
  · exact Or.inl same
  · exact Or.inr (intersect_strict algebra inventory complete left right same)

/-- Cartesian intersection is commutative, including the identity shortcut. -/
theorem intersect_comm (algebra : Conjunction Row) (left right : Rows Row) :
    intersect algebra left right = intersect algebra right left := by
  classical
  by_cases same : left = right
  · subst right; rfl
  · simp only [intersect, same, Ne.symm same, ↓reduceIte]
    funext row
    apply propext
    constructor <;> rintro ⟨a, b, presentA, presentB, result⟩
    · exact ⟨b, a, presentB, presentA, (algebra.comm b a).trans result⟩
    · exact ⟨b, a, presentB, presentA, (algebra.comm b a).trans result⟩

/-- A leaf forest uses the source child positions as finite indices. -/
abbrev Forest (Row : Type) (arity : Nat) := Fin arity → Rows Row

/-- The source seeds its right fold with the first projected node. -/
noncomputable def intersectList (algebra : Conjunction Row) : List (Rows Row) → Rows Row
  | [] => fun _ => False
  | first :: rest => rest.foldr (intersect algebra) first

/-- Simultaneous class edits use the old forest for every projected operand. -/
noncomputable def reduceClass (algebra : Conjunction Row) (paths : List (Fin arity)) (before : Forest Row arity) : Forest Row arity := by
  classical
  exact fun index => if index ∈ paths then
    intersect algebra (intersectList algebra ((paths.filter (· != index)).map before)) (before index)
    else before index

/-- Each changed coordinate of a complete simultaneous class edit strictly improves. -/
theorem class_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (paths : List (Fin arity)) (before : Forest Row arity) (index : Fin arity) :
    Improves algebra inventory (reduceClass algebra paths before index) (before index) := by
  classical
  unfold reduceClass
  split
  · rw [intersect_comm]
    exact intersect_improves algebra inventory complete _ _
  · exact improves_refl algebra inventory _

/-- The source applies its selected classes in right-fold order. -/
noncomputable def schedule (algebra : Conjunction Row) (classes : List (List (Fin arity)))
    (before : Forest Row arity) : Forest Row arity := classes.foldr (reduceClass algebra) before

/-- Whole schedules retain coordinate progress even when later classes overlap earlier classes. -/
theorem schedule_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (classes : List (List (Fin arity))) (before : Forest Row arity) (index : Fin arity) :
    Improves algebra inventory (schedule algebra classes before index) (before index) := by
  induction classes with
  | nil => exact improves_refl algebra inventory _
  | cons paths rest ih =>
      exact improves_trans algebra inventory _ _ _ ih (class_improves algebra inventory complete paths _ index)

/-- Sum a finite forest's exact leaf potentials. -/
noncomputable def forestPotential (algebra : Conjunction Row) (inventory : List Row) (forest : Forest Row arity) : Nat :=
  ((List.ofFn id).map (fun index => potential algebra inventory (forest index))).sum

/-- Equal potential sums under coordinate progress force equality at every listed position. -/
theorem sum_progress (algebra : Conjunction Row) (inventory : List Row) (positions : List Index)
    (before after : Index → Rows Row)
    (progress : ∀ index ∈ positions, Improves algebra inventory (after index) (before index)) :
    (positions.map (fun index => potential algebra inventory (after index))).sum ≤
      (positions.map (fun index => potential algebra inventory (before index))).sum ∧
    ((positions.map (fun index => potential algebra inventory (after index))).sum =
      (positions.map (fun index => potential algebra inventory (before index))).sum →
      ∀ index ∈ positions, after index = before index) := by
  induction positions with
  | nil => simp
  | cons index rest ih =>
      have head := progress index (by simp)
      have bound : potential algebra inventory (after index) ≤ potential algebra inventory (before index) := by
        rcases head with same | smaller
        · rw [same]
          exact Nat.le_refl _
        · exact Nat.le_of_lt smaller
      have tail := ih (fun other member => progress other (by simp [member]))
      simp only [List.map_cons, List.sum_cons]
      refine ⟨Nat.add_le_add bound tail.1, ?_⟩
      intro equal other member
      have tailEqual : (rest.map (fun index => potential algebra inventory (after index))).sum =
          (rest.map (fun index => potential algebra inventory (before index))).sum := by omega
      rcases List.mem_cons.mp member with rfl | present
      · rcases head with same | smaller
        · exact same
        · omega
      · exact tail.2 tailEqual other present

/-- Any changed whole forest with coordinate progress strictly decreases its finite sum. -/
theorem forest_strict (algebra : Conjunction Row) (inventory : List Row) (before after : Forest Row arity)
    (progress : ∀ index, Improves algebra inventory (after index) (before index)) (changed : after ≠ before) :
    forestPotential algebra inventory after < forestPotential algebra inventory before := by
  have summed := sum_progress algebra inventory (List.ofFn id) before after (fun index _ => progress index)
  apply Nat.lt_of_le_of_ne summed.1
  intro equal
  apply changed
  funext index
  exact summed.2 equal index (by simp)

/-- Empty remains empty under the exact source intersection shortcut. -/
theorem intersect_empty (algebra : Conjunction Row) (rows : Rows Row) :
    intersect algebra rows (fun _ => False) = (fun _ => False) := by
  classical
  by_cases same : rows = (fun _ => False)
  · simp [intersect, same]
  · simp only [intersect, same, ↓reduceIte]
    funext row
    simp [product]

/-- Empty propagation is a strict coordinate improvement unless that coordinate was empty. -/
theorem empty_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (rows : Rows Row) : Improves algebra inventory (fun _ => False) rows := by
  have improved := intersect_improves algebra inventory complete rows (fun _ => False)
  rwa [intersect_empty] at improved

/-- The source replaces every child with EmptyNode when one child is empty. -/
noncomputable def propagate (before : Forest Row arity) : Forest Row arity := by
  classical
  exact if ∃ index, before index = (fun _ => False) then fun _ _ => False else before

/-- Empty propagation preserves coordinate progress for the whole forest. -/
theorem propagate_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (before : Forest Row arity) (index : Fin arity) : Improves algebra inventory (propagate before index) (before index) := by
  unfold propagate
  split
  · exact empty_improves algebra inventory complete _
  · exact improves_refl algebra inventory _

/-- A leaf pass includes the empty-constraint shortcut and contradiction result.
All required direct children already exist because their indices are in Fin arity. -/
noncomputable def pass (algebra : Conjunction Row) (skip contradiction : Bool)
    (classes : List (List (Fin arity))) (before : Forest Row arity) : Forest Row arity :=
  if skip then before else if contradiction then fun _ _ => False else propagate (schedule algebra classes before)

/-- Every source branch of a leaf-forest pass retains coordinate progress. -/
theorem pass_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (skip contradiction : Bool) (classes : List (List (Fin arity))) (before : Forest Row arity) (index : Fin arity) :
    Improves algebra inventory (pass algebra skip contradiction classes before index) (before index) := by
  cases skip <;> cases contradiction
  · exact improves_trans algebra inventory _ _ _ (schedule_improves algebra inventory complete classes before index)
      (propagate_improves algebra inventory complete _ index)
  · exact empty_improves algebra inventory complete _
  · exact improves_refl algebra inventory _
  · exact improves_refl algebra inventory _

/-- Every changing complete source leaf pass strictly decreases the forest potential. -/
theorem pass_strict (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (skip contradiction : Bool) (classes : List (List (Fin arity))) (before : Forest Row arity)
    (changed : pass algebra skip contradiction classes before ≠ before) :
    forestPotential algebra inventory (pass algebra skip contradiction classes before) < forestPotential algebra inventory before :=
  forest_strict algebra inventory before _ (pass_improves algebra inventory complete skip contradiction classes before) changed

/-- Repeat the actual structural fixed-point test with an explicit proof bound. -/
noncomputable def run (algebra : Conjunction Row) (skip contradiction : Bool)
    (classes : List (List (Fin arity))) : Nat → Forest Row arity → Option (Forest Row arity)
  | 0, _ => none
  | fuel + 1, before => by
      classical
      exact let after := pass algebra skip contradiction classes before
        if after = before then some before else run algebra skip contradiction classes fuel after

/-- Every fixed direct-child leaf schedule reaches a structural fixed point. -/
theorem run_terminates (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (skip contradiction : Bool) (classes : List (List (Fin arity))) (before : Forest Row arity) :
    ∃ fuel after, run algebra skip contradiction classes fuel before = some after ∧
      pass algebra skip contradiction classes after = after ∧
      fuel ≤ forestPotential algebra inventory before + 1 := by
  classical
  let after := pass algebra skip contradiction classes before
  by_cases same : after = before
  · exact ⟨1, before, by simp [run, after] at same ⊢; exact same, same, by omega⟩
  · obtain ⟨fuel, final, finished, fixed, bounded⟩ := run_terminates algebra inventory complete skip contradiction classes after
    have smaller := pass_strict algebra inventory complete skip contradiction classes before same
    exact ⟨fuel + 1, final, by simpa only [run, show pass algebra skip contradiction classes before = after from rfl,
      same, ↓reduceIte] using finished, fixed, by change forestPotential algebra inventory after < _ at smaller; omega⟩
termination_by forestPotential algebra inventory before
decreasing_by exact pass_strict algebra inventory complete skip contradiction classes before same

/-- Canonical source guards supply the whole finite inventory and all row algebra laws. -/
theorem source_terminates (initial : List (SourceGuards.Guard FullSyntax.Formula))
    (skip contradiction : Bool) (classes : List (List (Fin arity)))
    (before : Forest (SourceLeafRowProgress.Row initial) arity) :
    ∃ fuel after, run (SourceLeafRowProgress.algebra initial) skip contradiction classes fuel before = some after ∧
      pass (SourceLeafRowProgress.algebra initial) skip contradiction classes after = after ∧
      fuel ≤ forestPotential (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial) before + 1 :=
  run_terminates (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial)
    (SourceLeafRowProgress.inventory_complete initial) skip contradiction classes before

end MicroCFTA.FiniteLeafForestProgress
