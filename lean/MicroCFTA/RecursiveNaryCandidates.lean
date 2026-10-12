import MicroCFTA.RecursiveNaryInverse

/-!
# Source bounds, order, and distinctness for all n-ary candidates

These contracts include true and false checked flags. The root counts come
from the actual typed value index. No inverse contract is used for them.
-/
namespace MicroCFTA.RecursiveNaryCandidates
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct
open RecursiveNaryFields RecursiveNaryInverse
open RecursiveNaryBody (valueRecipe termBody term_guard)

/-- Every finite child candidate is within its own declared size class. -/
def LeavesBounded [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) : Body Root Symbol Value → Prop
  | .finite source => RecursiveNaryChoice.Bounded (RecursiveCallbackAlignment.finite callbacks source)
  | .occurrence => True
  | .map _ inner | .pay inner | .label _ inner => LeavesBounded callbacks inner
  | .choice _ branches => ∀ index, LeavesBounded callbacks (branches index)
  | .ap functions arguments => LeavesBounded callbacks functions ∧ LeavesBounded callbacks arguments

/-- Every finite child callback is in the source checked-row order. -/
def LeavesOrdered [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) : Body Root Symbol Value → Prop
  | .finite source => ∀ view wanted,
      ((RecursiveCallbackAlignment.finite callbacks source).positions view wanted).Pairwise (fun a b => before a b)
  | .occurrence => True
  | .map _ inner | .pay inner | .label _ inner => LeavesOrdered callbacks inner
  | .choice _ branches => ∀ index, LeavesOrdered callbacks (branches index)
  | .ap functions arguments => LeavesOrdered callbacks functions ∧ LeavesOrdered callbacks arguments

/-- Every finite child callback has distinct positions before any replay filter. -/
def LeavesDistinct [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) : Body Root Symbol Value → Prop
  | .finite source => RecursiveNaryChoice.Unique (RecursiveCallbackAlignment.finite callbacks source)
  | .occurrence => True
  | .map _ inner | .pay inner | .label _ inner => LeavesDistinct callbacks inner
  | .choice _ branches => ∀ index, LeavesDistinct callbacks (branches index)
  | .ap functions arguments => LeavesDistinct callbacks functions ∧ LeavesDistinct callbacks arguments

/-- Each n-ary source operation keeps every candidate in range. -/
theorem compiled_bounded [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (root : Finite Symbol)
    (rootBounded : RecursiveNaryChoice.Bounded root) (recipe : Body Root Symbol Value)
    (leaves : LeavesBounded callbacks recipe) : RecursiveNaryChoice.Bounded (compile callbacks root recipe) := by
  induction recipe with
  | finite source => exact leaves
  | occurrence => exact rootBounded
  | map transform inner ih => exact ih leaves
  | pay inner ih | label symbol inner ih => exact RecursiveFieldCombinators.field_bounded _ (ih leaves)
  | ap functions arguments ihf iha => exact RecursiveFieldCombinators.field_bounded _ ⟨ihf leaves.1, iha leaves.2⟩
  | choice count branches ih =>
      apply RecursiveNaryChoice.field_bounded
      intro child present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
      exact ih index (leaves index)

/-- Each n-ary source operation keeps source checked-row order. -/
theorem compiled_ordered [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (root : Finite Symbol)
    (rootOrdered : ∀ view wanted, (root.positions view wanted).Pairwise (fun a b => before a b))
    (recipe : Body Root Symbol Value) (leaves : LeavesOrdered callbacks recipe) :
    ∀ view wanted, ((compile callbacks root recipe).positions view wanted).Pairwise (fun a b => before a b) := by
  induction recipe with
  | finite source => exact leaves
  | occurrence => exact rootOrdered
  | map transform inner ih => exact ih leaves
  | pay inner ih | label symbol inner ih => exact RecursiveFieldCombinators.field_ordered _ (ih leaves)
  | ap functions arguments ihf iha => exact RecursiveFieldCombinators.field_ordered _ ⟨ihf leaves.1, iha leaves.2⟩
  | choice count branches ih => exact RecursiveNaryChoice.positions_ordered _

/-- Each n-ary source operation keeps distinct valid positions. -/
theorem compiled_distinct [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (root : Finite Symbol)
    (rootBounded : RecursiveNaryChoice.Bounded root) (rootDistinct : RecursiveNaryChoice.Unique root)
    (recipe : Body Root Symbol Value) (bounded : LeavesBounded callbacks recipe)
    (distinct : LeavesDistinct callbacks recipe) : RecursiveNaryChoice.Unique (compile callbacks root recipe) := by
  induction recipe with
  | finite source => exact distinct
  | occurrence => exact rootDistinct
  | map transform inner ih => exact ih bounded distinct
  | pay inner ih | label symbol inner ih =>
      exact RecursiveFieldCombinators.field_distinct _ (compiled_bounded callbacks root rootBounded inner bounded) (ih bounded distinct)
  | ap functions arguments ihf iha =>
      exact RecursiveFieldCombinators.field_distinct _
        ⟨compiled_bounded callbacks root rootBounded functions bounded.1,
          compiled_bounded callbacks root rootBounded arguments bounded.2⟩
        ⟨ihf bounded.1 distinct.1, iha bounded.2 distinct.2⟩
  | choice count branches ih =>
      apply RecursiveNaryChoice.field_unique
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact compiled_bounded callbacks root rootBounded (branches index) (bounded index)
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact ih index (bounded index) (distinct index)

/-- The source count knot follows from the independent typed class equation. -/
theorem count_knot [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (callback : Callback Symbol) (size : Nat) :
    rootCounts body size = (compile callbacks (rootField body callback) body).counts size := by
  have aligned := congrArg List.length (compiled_classes callbacks _ (root_indexed body callback) body size)
  rw [finite_length] at aligned
  rw [show finiteClass (rootField body callback) = RecursiveSource.languageClass (termBody body) from
    funext (root_class body callback)] at aligned
  rw [rootCounts, RecursiveNaryBody.class_counts, RecursiveSource.family_count,
    RecursiveSourceUnfolding.languageClass_unfold (termBody body) (term_guard body accepted)]
  simp only [termBody, RecursiveSource.values, List.length_map]
  exact aligned.symm

/-- Every fuel-bounded call retains only valid source class positions. -/
theorem fuel_bounded [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (leaves : LeavesBounded callbacks body) (fuel : Nat) :
    RecursiveNaryChoice.Bounded (rootField body (fuelPositions callbacks body fuel)) := by
  induction fuel with
  | zero => intro view wanted row member; simp [rootField, fuelPositions] at member
  | succ fuel ih =>
      intro view wanted row member
      change row ∈ fuelPositions callbacks body (fuel + 1) view wanted at member
      rw [fuelPositions] at member
      dsimp only at member
      split at member
      · simp at member
      · have bound := compiled_bounded callbacks _ ih body leaves .whole _ row member
        change row.1.rank < rootCounts body row.1.size
        rw [count_knot callbacks body accepted (fuelPositions callbacks body fuel)]
        exact bound

/-- Every fuel-bounded call retains the source checked-row order. -/
theorem fuel_ordered [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (leaves : LeavesOrdered callbacks body) (fuel : Nat) :
    ∀ view wanted, (fuelPositions callbacks body fuel view wanted).Pairwise (fun a b => before a b) := by
  induction fuel with
  | zero => intro view wanted; exact List.Pairwise.nil
  | succ fuel ih =>
      intro view wanted
      rw [fuelPositions]
      dsimp only
      split
      · exact List.Pairwise.nil
      · exact compiled_ordered callbacks _ ih body leaves .whole _

/-- Every fuel-bounded call retains distinct source positions for both flags. -/
theorem fuel_distinct [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (bounded : LeavesBounded callbacks body) (distinct : LeavesDistinct callbacks body) (fuel : Nat) :
    RecursiveNaryChoice.Unique (rootField body (fuelPositions callbacks body fuel)) := by
  induction fuel with
  | zero => intro view wanted; exact List.Pairwise.nil
  | succ fuel ih =>
      intro view wanted
      change Distinct (fuelPositions callbacks body (fuel + 1) view wanted)
      rw [fuelPositions]
      dsimp only
      split
      · exact List.Pairwise.nil
      · exact compiled_distinct callbacks _ (fuel_bounded callbacks body accepted bounded fuel) ih body bounded distinct .whole _

/-- The requested-height inverse keeps all candidates inside the value-index interval. -/
theorem positions_bounded [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (bounded : LeavesBounded callbacks body) (view : View) (wanted : List (EngineTerm Symbol))
    (row : Checked) (member : row ∈ RecursiveNaryInverse.positions callbacks body view wanted) :
    row.1.rank < rootCounts body row.1.size :=
  fuel_bounded callbacks body accepted bounded (forestHeight wanted) view wanted row member

/-- The requested-height inverse retains the complete source candidate order. -/
theorem positions_ordered [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (ordered : LeavesOrdered callbacks body) (view : View) (wanted : List (EngineTerm Symbol)) :
    (RecursiveNaryInverse.positions callbacks body view wanted).Pairwise (fun a b => before a b) :=
  fuel_ordered callbacks body ordered (forestHeight wanted) view wanted

/-- The requested-height inverse cannot repeat a valid class position. -/
theorem positions_distinct [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (bounded : LeavesBounded callbacks body) (distinct : LeavesDistinct callbacks body)
    (view : View) (wanted : List (EngineTerm Symbol)) :
    Distinct (RecursiveNaryInverse.positions callbacks body view wanted) :=
  fuel_distinct callbacks body accepted bounded distinct (forestHeight wanted) view wanted

end MicroCFTA.RecursiveNaryCandidates
