import MicroCFTA.EqualityLeafProjectionTermination

/-!
# Canonical leaf residuals that survive literal Bottom rejection

The physical source constructor removes a literal Bottom guard. Restrict
canonical residual rows to non-Bottom guards before requiring an injective
leaf representation. Canonical conjunction preserves this restriction.
-/
namespace MicroCFTA.EqualityLeafProjectionRows
open SourceGuards FullSyntax GuardConjunction

/-- A normalized guard with only Bottom as an outer atom is literally Bottom. -/
theorem only_bottom (guard : Guard Formula)
    (normalized : normalize GuardStructuralOrder.le guard = guard)
    (present : (.bottom : Guard Formula) ∈ atoms guard)
    (only : ∀ atom ∈ atoms guard, atom = .bottom) : guard = .bottom := by
  have same := normalize_eq GuardStructuralOrder.le GuardStructuralOrder.le_trans GuardStructuralOrder.le_total
    GuardStructuralOrder.le_antisymm guard .bottom (fun atom => by
      constructor
      · intro member
        simp only [atoms, List.mem_singleton]
        exact only atom member
      · intro member
        have equal : atom = .bottom := by simpa only [atoms, List.mem_singleton] using member
        simpa only [equal] using present)
  rw [normalized] at same
  simpa only [normalize, atoms, canonical, List.eraseDups_cons, List.filter_nil, List.eraseDups_nil,
    List.mergeSort_singleton, conjoin] using same

/-- Canonical source conjunction cannot create a literal Bottom from two surviving rows. -/
theorem merge_ne_bottom (first second : Guard Formula)
    (firstNormalized : normalize GuardStructuralOrder.le first = first)
    (secondNormalized : normalize GuardStructuralOrder.le second = second)
    (firstLive : first ≠ .bottom) (secondLive : second ≠ .bottom) :
    merge GuardStructuralOrder.le first second ≠ .bottom := by
  intro equal
  have bottomMember : (.bottom : Guard Formula) ∈ atoms (merge GuardStructuralOrder.le first second) := by
    rw [equal]
    simp [atoms]
  have only : ∀ atom, atom ∈ atoms first ∨ atom ∈ atoms second → atom = .bottom := by
    intro atom member
    have combined := (merge_mem GuardStructuralOrder.le first second atom).mpr member
    simpa only [equal, atoms, List.mem_singleton] using combined
  rcases (merge_mem GuardStructuralOrder.le first second .bottom).mp bottomMember with left | right
  · exact firstLive (only_bottom first firstNormalized left (fun atom member => only atom (Or.inl member)))
  · exact secondLive (only_bottom second secondNormalized right (fun atom member => only atom (Or.inr member)))

/-- A physical canonical leaf row is not rejected by the literal Bottom check. -/
def Row (initial : List (Guard Formula)) := {row : SourceLeafRowProgress.Row initial // row.val ≠ .bottom}

/-- Source conjunction stays inside the physically retained residual carrier. -/
def join (initial : List (Guard Formula)) (first second : Row initial) : Row initial :=
  ⟨SourceLeafRowProgress.join initial first.val second.val,
    merge_ne_bottom first.val.val second.val.val first.val.property.1 second.val.property.1 first.property second.property⟩

/-- Row conjunction inherits the checked source associativity, commutativity, and self law. -/
def algebra (initial : List (Guard Formula)) : FiniteRowIntersection.Conjunction (Row initial) where
  join := join initial
  assoc := fun first second third => Subtype.ext ((SourceLeafRowProgress.algebra initial).assoc first.val second.val third.val)
  comm := fun first second => Subtype.ext ((SourceLeafRowProgress.algebra initial).comm first.val second.val)
  idem := fun first => Subtype.ext ((SourceLeafRowProgress.algebra initial).idem first.val)

/-- Filter the generated source inventory by the actual literal Bottom rejection. -/
noncomputable def inventory (initial : List (Guard Formula)) : List (Row initial) := by
  classical
  exact (SourceLeafRowProgress.inventory initial).filterMap fun row =>
    if live : row.val ≠ .bottom then some ⟨row, live⟩ else none

/-- Every surviving canonical residual is present in the filtered finite inventory. -/
theorem inventory_complete (initial : List (Guard Formula)) (row : Row initial) : row ∈ inventory initial := by
  unfold inventory
  apply List.mem_filterMap.mpr
  refine ⟨row.val, SourceLeafRowProgress.inventory_complete initial row.val, ?_⟩
  rw [dite_eq_left row.property]
  exact congrArg some (Subtype.ext rfl)

/-- Literal Bottom filtering cannot increase the derived source inventory bound. -/
theorem inventory_length (initial : List (Guard Formula)) :
    (inventory initial).length ≤ 2 ^ (SourceLeafRowProgress.basis initial).length := by
  rw [← SourceLeafRowProgress.inventory_length initial]
  exact List.length_filterMap_le _ _

/-- The physical row restriction retains the projected-leaf source identity bound. -/
theorem source_terminates (initial : List (Guard Formula))
    (source : EqualityLeafProjectionSyntax.Source Tag (FiniteLeafSymbolsProgress.Node (Row initial) symbols) Node)
    (laws : EqualityLeafProjectionSyntax.ConstructorLaws source (FiniteLeafSymbolsProgress.intersect (algebra initial)))
    (read : EqualityLeafProjectionSyntax.Path → List Node → FiniteLeafSymbolsProgress.Node (Row initial) symbols)
    (skip contradiction : Bool) (classes : List (List EqualityLeafProjectionSyntax.Path))
    (before : List (EqualityLeafProjectionSyntax.Tree Tag (FiniteLeafSymbolsProgress.Node (Row initial) symbols)))
    (valid : EqualityLeafProjectionSyntax.Endpoints classes.flatten before) :
    ∃ fuel result, EqualityLeafProjectionSchedule.sourceRun source (FiniteLeafSymbolsProgress.intersect (algebra initial))
        FiniteLeafSymbolsProgress.empty read skip contradiction classes fuel (EqualityLeafProjectionSyntax.lowerForest source before) = some result ∧
      EqualityLeafProjectionSchedule.sourcePass source (FiniteLeafSymbolsProgress.intersect (algebra initial))
        FiniteLeafSymbolsProgress.empty read skip contradiction classes result = result ∧
      fuel ≤ EqualityLeafProjectionSyntax.forestWeight
        (EqualityLeafProjectionSyntax.leafRank (algebra initial) (inventory initial)) before + 1 :=
  EqualityLeafProjectionSchedule.source_terminates source
    (EqualityLeafProjectionSyntax.leafRank (algebra initial) (inventory initial))
    (FiniteLeafSymbolsProgress.intersect (algebra initial)) FiniteLeafSymbolsProgress.empty laws
    (EqualityLeafProjectionSyntax.source_leaf_progress (algebra initial) (inventory initial) (inventory_complete initial))
    read skip contradiction classes before valid

end MicroCFTA.EqualityLeafProjectionRows
