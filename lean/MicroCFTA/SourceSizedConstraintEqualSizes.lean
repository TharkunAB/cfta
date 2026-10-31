import MicroCFTA.SourceSizedPrefixEqualSizes
import MicroCFTA.SourceEqualityGuardReadback
import Init.Data.List.Nat.TakeDrop

/-!
# Numeric size filtering from the current full constraint

The view uses the actual complete equality accessor on natural source paths.
Complete constraint acceptance derives numeric acceptance of child node sizes.
The signed Haskell constraint and Set representation adapters remain separate.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceSizedConstraintEqualSizes
open Language RecursiveSize
open SourceSizedPrefixEqualSizes (EqualityView directChildren readSizes allSame)
variable {Formula Symbol : Type}

/-- Render the actual full accessor result into the existing numeric view. -/
noncomputable def view (constraint : SourceSymbolicIndex.Constraint Formula) : EqualityView :=
  (SourceCompactGuards.sourceEqualities constraint).map (List.map (List.map (List.map Int.ofNat)))

/-- Filter with the current full constraint, including its positive guard equalities. -/
noncomputable def equalSizes {Size : Type} [DecidableEq Size]
    (constraint : SourceSymbolicIndex.Constraint Formula) (parts : List Size) : Bool :=
  SourceSizedPrefixEqualSizes.equalSizes (view constraint) parts

/-- Exact Int embedding preserves the produced full-constraint numeric filter. -/
theorem equalSizes_cast (constraint : SourceSymbolicIndex.Constraint Formula) (parts : List Nat) :
    equalSizes constraint (parts.map Int.ofNat) = equalSizes constraint parts :=
  SourceSizedPrefixEqualSizes.equalSizes_cast (view constraint) parts

private theorem singleton_size (symbol : Symbol) (children : List (Term Symbol)) (index : Nat)
    (common : Term Symbol) (found : (Term.node symbol children).atPath [index] = some common) :
    SourceSizedPrefixEqualSizes.sizeOf (children.map nodeSize) (index : Int) = some (nodeSize common) := by
  have nonnegative : 0 ≤ (index : Int) := by omega
  simp only [SourceSizedPrefixEqualSizes.sizeOf, ite_eq_left nonnegative]
  change ((children.map nodeSize).drop index).head? = some (nodeSize common)
  rw [← List.map_drop, List.head?_map, List.head?_drop]
  have located : children[index]? = some common := by simpa [Term.atPath] using found
  rw [located]
  rfl

private theorem direct_member (paths : List (List Nat)) (index : Int)
    (member : index ∈ directChildren (paths.map (List.map Int.ofNat))) :
    ∃ natural, [natural] ∈ paths ∧ index = (natural : Int) := by
  obtain ⟨path, present, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨natural, listed, same⟩ := List.mem_map.mp present
  subst path
  cases natural with
  | nil => cases selected
  | cons first rest =>
      cases rest with
      | nil => exact ⟨first, listed, (Option.some.inj selected).symm⟩
      | cons second rest => cases selected

private theorem read_common (parts : List Nat) (common : Nat) (indices : List Int) :
    (∀ index ∈ indices, SourceSizedPrefixEqualSizes.sizeOf parts index = some common) →
      ∃ values, readSizes parts indices = some values ∧ ∀ value ∈ values, value = common := by
  induction indices with
  | nil => intro _; exact ⟨[], rfl, by intro value impossible; cases impossible⟩
  | cons first rest ih =>
      intro lookups
      obtain ⟨values, found, every⟩ := ih (fun index member => lookups index (List.mem_cons_of_mem _ member))
      refine ⟨common :: values, ?_, ?_⟩
      · simp [readSizes, lookups first List.mem_cons_self, found]
      · intro value member
        rcases List.mem_cons.mp member with atFirst | inRest
        · exact atFirst
        · exact every value inRest

private theorem numeric_common (parts : List Nat) (common : Nat) (indices : List Int)
    (lookups : ∀ index ∈ indices, SourceSizedPrefixEqualSizes.sizeOf parts index = some common) :
    allSame (readSizes parts indices) = true := by
  obtain ⟨values, found, every⟩ := read_common parts common indices lookups
  rw [found]
  cases values with
  | nil => rfl
  | cons first rest =>
      change rest.all (fun value => decide (value = first)) = true
      apply List.all_eq_true.mpr
      intro value member
      simpa only [decide_eq_true_eq] using
        (every value (List.mem_cons_of_mem _ member)).trans (every first List.mem_cons_self).symm

private theorem class_filter (symbol : Symbol) (children : List (Term Symbol)) (paths : List (List Nat))
    (satisfied : Symbolic.ClassSatisfied (.node symbol children) paths) :
    allSame (readSizes (children.map nodeSize) (directChildren (paths.map (List.map Int.ofNat)))) = true := by
  cases paths with
  | nil => rfl
  | cons first rest =>
      obtain ⟨common, head, tail⟩ := satisfied
      have located : ∀ path ∈ first :: rest, (Term.node symbol children).atPath path = some common := by
        intro path member
        rcases List.mem_cons.mp member with atFirst | inRest
        · simpa only [atFirst] using head
        · exact tail path inRest
      apply numeric_common _ (nodeSize common)
      intro index member
      obtain ⟨natural, present, same⟩ := direct_member (first :: rest) index member
      rw [same]
      exact singleton_size symbol children natural common (located [natural] present)

/-- Actual complete acceptance makes the child node-size allocation pass the produced filter. -/
theorem accepted_equal_sizes [DecidableEq Formula]
    (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (symbol : SourceObservations.Label Formula)
    (children : List (Term (SourceObservations.Label Formula)))
    (accepted : SourceSymbolicIndex.acceptsConstraint formulas solver constraint (.node symbol children) = true) :
    equalSizes constraint (children.map nodeSize) = true := by
  classical
  cases produced : SourceCompactGuards.sourceEqualities constraint with
  | none => simp only [equalSizes, view, produced, Option.map_none, SourceSizedPrefixEqualSizes.equalSizes]
  | some classes =>
      have allClasses : classes.all (SymbolicDriver.classTest (.node symbol children)) = true := by
        have payload := SourceEqualityGuardReadback.accepted_equalities formulas solver constraint
          (SourceEqualityGuardReadback.active cached) (.node symbol children) accepted
        simpa only [produced, ConstraintIndicators.equalityValue] using payload
      simp only [equalSizes, view, produced, Option.map_some, SourceSizedPrefixEqualSizes.equalSizes,
        List.all_map, Function.comp_def]
      apply List.all_eq_true.mpr
      intro paths member
      apply class_filter symbol children paths
      have checked := List.all_eq_true.mp allClasses paths member
      simpa only [SymbolicDriver.classTest, decide_eq_true_eq] using checked

end MicroCFTA.SourceSizedConstraintEqualSizes
