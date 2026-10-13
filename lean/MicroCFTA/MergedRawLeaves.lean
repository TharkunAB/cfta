import MicroCFTA.EqualityRawLeafInventory

/-!
# Merged peer targets in the finite raw-leaf carrier

At a nullary symbol, the source retains the one original row or replaces
multiple distinct rows with Top. This preserves the existing finite carrier.
The old physical target worker does not perform this step. These results do
not silently extend that worker's complete-record correspondence.
-/
namespace MicroCFTA.MergedRawLeaves
open SourceGuards FullSyntax EqualityRawLeafInventory

/-- The unconstrained row already belongs to every source-generated finite inventory. -/
def top (initial : List (Guard Formula)) : Row initial :=
  ⟨⟨.top, by simp [GuardConjunction.atoms]⟩, Or.inr (by simp [GuardConjunction.normalize, GuardConjunction.canonical,
    GuardConjunction.atoms, GuardConjunction.conjoin]), by
    simp [EqualityRawLeafConstruction.accepted, SourceCompactGuards.sourceEqualities,
      EqualityLeafProjectionAdmittedSource.fitsLeaf, SourceCompactGuards.positiveNormalized]⟩

/-- The nullary source group operation, after physical duplicate removal. -/
def merge (leaf : Leaf initial symbols) : Leaf initial symbols := fun symbol row =>
  (leaf symbol row ∧ ∀ other, leaf symbol other → other = row) ∨
    (row = top initial ∧ ∃ first second,
      leaf symbol first ∧ leaf symbol second ∧ first ≠ second)

/-- A merged symbol has at most one complete raw row. -/
theorem unique (leaf : Leaf initial symbols) (symbol : Fin symbols) (first second : Row initial)
    (left : merge leaf symbol first) (right : merge leaf symbol second) : first = second := by
  rcases left with ⟨present, only⟩ | ⟨rfl, a, b, aMember, bMember, different⟩
  · rcases right with ⟨member, _⟩ | ⟨_, a, b, aMember, bMember, different⟩
    · exact (only second member).symm
    · exact False.elim (different ((only a aMember).trans (only b bMember).symm))
  · rcases right with ⟨member, only⟩ | ⟨same, _⟩
    · exact False.elim (different ((only a aMember).trans (only b bMember).symm))
    · exact same.symm

/-- A source symbol survives exactly when it had an original row. -/
theorem support (leaf : Leaf initial symbols) (symbol : Fin symbols) :
    (∃ row, merge leaf symbol row) ↔ ∃ row, leaf symbol row := by
  classical
  constructor
  · rintro ⟨row, ⟨present, _⟩ | ⟨_, first, second, present, _⟩⟩
    · exact ⟨row, present⟩
    · exact ⟨first, present⟩
  · rintro ⟨row, present⟩
    by_cases only : ∀ other, leaf symbol other → other = row
    · exact ⟨row, Or.inl ⟨present, only⟩⟩
    · have other : ∃ other, leaf symbol other ∧ other ≠ row := by
        exact Classical.not_forall.mp only |>.imp (fun other h => by simpa using h)
      obtain ⟨other, member, different⟩ := other
      exact ⟨top initial, Or.inr ⟨rfl, other, row, member, present, different⟩⟩

/-- A predicate with one complete row per symbol needs no merge. -/
theorem unchanged (leaf : Leaf initial symbols)
    (single : ∀ symbol first second, leaf symbol first → leaf symbol second → first = second) :
    merge leaf = leaf := by
  funext symbol row
  apply propext
  constructor
  · rintro (⟨present, _⟩ | ⟨_, first, second, left, right, different⟩)
    · exact present
    · exact False.elim (different (single symbol first second left right))
  · intro present
    exact Or.inl ⟨present, fun other member => single symbol other row member present⟩

/-- Merging the same finite raw leaf twice has no further effect. -/
theorem idempotent (leaf : Leaf initial symbols) : merge (merge leaf) = merge leaf :=
  unchanged (merge leaf) (unique leaf)

/-- The source group can add accepted terms but cannot remove one. -/
theorem covers (leaf : Leaf initial symbols) (symbol : Fin symbols)
    (holds : Row initial → Prop) (topHolds : holds (top initial))
    (accepted : ∃ row, leaf symbol row ∧ holds row) :
    ∃ row, merge leaf symbol row ∧ holds row := by
  classical
  obtain ⟨row, present, accepted⟩ := accepted
  by_cases only : ∀ other, leaf symbol other → other = row
  · exact ⟨row, Or.inl ⟨present, only⟩, accepted⟩
  · have other : ∃ other, leaf symbol other ∧ other ≠ row := by
      exact Classical.not_forall.mp only |>.imp (fun other h => by simpa using h)
    obtain ⟨other, member, different⟩ := other
    exact ⟨top initial, Or.inr ⟨rfl, other, row, member, present, different⟩, topHolds⟩

/-- Each target-first intersection still has the derived finite source progress measure. -/
theorem merged_target_progress (target before : Leaf initial symbols) :
    EqualityLeafProjectionSyntax.Progress rank (intersect (merge target) before) before :=
  leaf_progress (merge target) before

end MicroCFTA.MergedRawLeaves
