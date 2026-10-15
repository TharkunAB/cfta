import MicroCFTA.SourceEqualityConstraintOrigins

/-!
# Finite source guard fields from original literal atoms

Keep each original guard field, including noncanonical fields. All later
conjunctions use the actual source normalizer. Their outer atoms come from
the original literal fields. A finite list of canonical selections contains
every such result.
-/
namespace MicroCFTA.SourceEqualityConstraintGuardInventory
open SourceObservations SourceSymbolicIndex
open SourceEqualityConstraintOrigins
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Guard" => SourceGuards.Guard FullSyntax.Formula
local notation "sourceTop" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "order" => GuardStructuralOrder.le
local instance : DecidableEq Guard := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Enumerate every selection of input positions in their original order. -/
def selections {α : Type} : List α → List (List α)
  | [] => [[]]
  | first :: rest => selections rest ++ (selections rest).map (first :: ·)

/-- Every Boolean filter is one of the explicit finite selections. -/
theorem filter_mem_selections {α : Type} (items : List α) (keep : α → Bool) :
    items.filter keep ∈ selections items := by
  induction items with
  | nil => simp [selections]
  | cons first rest ih =>
      cases chosen : keep first with
      | false => simpa only [List.filter_cons, chosen, Bool.false_eq_true, ↓reduceIte, selections] using
          List.mem_append_left ((selections rest).map (first :: ·)) ih
      | true =>
          simp only [List.filter_cons, chosen, ↓reduceIte, selections]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨rest.filter keep, ih, rfl⟩)

/-- Flatten only the outer conjunctions in the original complete literal fields. -/
def atoms (literals : List Constraint) : List Guard :=
  literals.flatMap (fun literal => GuardConjunction.atoms literal.guard)

/-- Preserve literal fields and enumerate every canonical subset conjunction. -/
def inventory (literals : List Constraint) : List Guard :=
  literals.map (·.guard) ++ .top :: (selections (atoms literals)).map
    (fun selected => GuardConjunction.conjoin (GuardConjunction.canonical order selected))

/-- Every atom of an actual derived constraint occurs in an original literal field. -/
theorem atoms_original (literals : List Constraint) (constraint : Constraint)
    (derived : Derived literals sourceTop conjoin constraint) (atom : Guard)
    (member : atom ∈ GuardConjunction.atoms constraint.guard) : atom ∈ atoms literals := by
  induction derived with
  | literal present => exact List.mem_flatMap.mpr ⟨_, present, member⟩
  | top => simp [SourceEqualityConstraintConstructors.top, GuardConjunction.atoms] at member
  | @conjunction first second firstDerived secondDerived firstIH secondIH =>
      change atom ∈ GuardConjunction.atoms (GuardConjunction.merge order first.guard second.guard) at member
      rcases (GuardConjunction.merge_mem order first.guard second.guard atom).mp member with member | member
      · exact firstIH member
      · exact secondIH member

/-- Each actual source conjunction produces a canonical guard field. -/
theorem conjunction_canonical (first second : Constraint) :
    GuardConjunction.normalize order (conjoin first second).guard = (conjoin first second).guard := by
  exact GuardConjunction.normalize_idempotent order GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm (.and [first.guard, second.guard])

/-- A derived field is an unchanged original field or a canonical source conjunction. -/
theorem original_or_canonical (literals : List Constraint) (constraint : Constraint)
    (derived : Derived literals sourceTop conjoin constraint) :
    constraint.guard ∈ literals.map (·.guard) ∨
      GuardConjunction.normalize order constraint.guard = constraint.guard := by
  cases derived with
  | literal present => exact Or.inl (List.mem_map.mpr ⟨_, present, rfl⟩)
  | top => exact Or.inr (by simp [SourceEqualityConstraintConstructors.top,
      GuardConjunction.normalize, GuardConjunction.atoms, GuardConjunction.canonical, GuardConjunction.conjoin])
  | conjunction first second => exact Or.inr (conjunction_canonical _ _)

/-- A canonical field with original atoms is one explicit finite subset conjunction. -/
theorem canonical_mem_inventory (literals : List Constraint) (guard : Guard)
    (original : ∀ atom ∈ GuardConjunction.atoms guard, atom ∈ atoms literals)
    (canonical : GuardConjunction.normalize order guard = guard) : guard ∈ inventory literals := by
  let selected := (atoms literals).filter (fun atom => decide (atom ∈ GuardConjunction.atoms guard))
  have selectedMember : selected ∈ selections (atoms literals) := filter_mem_selections _ _
  have same : ∀ atom, atom ∈ GuardConjunction.atoms guard ↔ atom ∈ selected := by
    intro atom
    simp only [selected, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun member => ⟨original atom member, member⟩, And.right⟩
  have normalized : GuardConjunction.canonical order (GuardConjunction.atoms guard) =
      GuardConjunction.canonical order selected :=
    GuardConjunction.canonical_ext order GuardStructuralOrder.le_trans GuardStructuralOrder.le_total
      GuardStructuralOrder.le_antisymm _ _ same
  have rebuilt : GuardConjunction.conjoin (GuardConjunction.canonical order selected) = guard := by
    rw [← normalized]
    exact canonical
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨selected, selectedMember, rebuilt⟩

/-- Every actual derived guard field occurs in the finite original guard inventory. -/
theorem derived_mem_inventory (literals : List Constraint) (constraint : Constraint)
    (derived : Derived literals sourceTop conjoin constraint) : constraint.guard ∈ inventory literals := by
  rcases original_or_canonical literals constraint derived with literal | canonical
  · exact List.mem_append_left _ literal
  · exact canonical_mem_inventory literals constraint.guard (atoms_original literals constraint derived) canonical

end MicroCFTA.SourceEqualityConstraintGuardInventory
