import MicroCFTA.EqualityLeafProjectionRuntimeForest

/-!
# Allocation-free runtime empty propagation

A contradictory class or an empty root erases the complete child forest.
The erased occurrence witness reconstructs without cache requests and
retains every endpoint invariant.
-/
namespace MicroCFTA.EqualityLeafProjectionRuntimeEmpty
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Tree Path ChildAt Progress forestWeight)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionTrim
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

/-- The source replaces each root slot with literal EmptyNode. -/
def erase (values : List (Value Symbol Guard)) : List (Value Symbol Guard) := values.map (fun _ => .empty)

/-- The source propagates any literal empty root through the entire forest. -/
def propagate (values : List (Value Symbol Guard)) : List (Value Symbol Guard) :=
  if values.any (fun value => value.referenceOf == .empty) then erase values else values

/-- Empty propagation tests exactly literal EmptyNode membership. -/
theorem empty_test (values : List (Value Symbol Guard)) :
    values.any (fun value => value.referenceOf == .empty) = true ↔ .empty ∈ values := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨value, member, empty⟩
    exact (EqualityLeafProjectionPhysical.reference_empty value).mp (beq_iff_eq.mp empty) ▸ member
  · intro member
    exact ⟨.empty, member, rfl⟩

/-- Empty occurrence roots retain the same label and leaf carrier types. -/
def eraseForest (forest : List (Tree Label Payload)) : List (Tree Label Payload) :=
  forest.map (fun _ => .empty)

/-- Erasure trims every original occurrence while retaining forest arity. -/
theorem erase_trim (forest : List (Tree Label Payload)) : TrimForest (eraseForest forest) forest := by
  induction forest with
  | nil => exact .nil
  | cons tree rest ih => exact .cons (.empty tree) ih

/-- Erased physical roots reconstruct without allocation in the unchanged source cache. -/
theorem erase_represented [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Payload → Work Symbol Guard (Value Symbol Guard))
    (forest : List (Tree (Tag Symbol Guard) Payload)) (state : State Symbol Guard) (valid : Valid state)
    (values : List (Value Symbol Guard)) (represented : RepresentsForest leaf forest state values) :
    RepresentsForest leaf (eraseForest forest) state (erase values) := by
  induction forest generalizing values with
  | nil =>
      have same : values = [] := (congrArg (fun result : List (Value Symbol Guard) × State Symbol Guard => result.1) represented).symm
      subst values
      rfl
  | cons first rest ih =>
      obtain ⟨value, tail, rfl, _, tailRep⟩ := forest_decompose leaf first rest state valid values represented
      exact forest_intro leaf .empty _ state .empty (erase tail) rfl (ih tail tailRep)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Contradiction erasure has exact runtime representation and strict rank on physical change. -/
theorem erase_progress
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    RepresentsForest build (eraseForest forest) state (erase values) ∧
      Progress (forestWeight rank) (eraseForest forest) forest ∧
      (∀ index path, ChildAt index path (eraseForest forest)) ∧
      ((erase values).map Value.referenceOf ≠ values.map Value.referenceOf →
        forestWeight rank (eraseForest forest) < forestWeight rank forest) := by
  have output := erase_represented build forest state facts.coherent.valid values represented
  have progress := EqualityLeafProjectionTrim.forest_progress rank (erase_trim forest)
  exact ⟨output, progress, fun index path => EqualityLeafProjectionSyntax.empty_children index path forest,
    EqualityLeafProjectionRuntimeForest.physical_strict forest _ (.pure ()) state facts values (erase values) represented output progress⟩

/-- Source empty propagation retains actual cache state and cannot increase occurrence potential. -/
theorem propagate_progress
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    ∃ trimmed, RepresentsForest build trimmed state (propagate values) ∧ Progress (forestWeight rank) trimmed forest ∧
      (∀ index path, ChildAt index path forest → ChildAt index path trimmed) ∧
      ((propagate values).map Value.referenceOf ≠ values.map Value.referenceOf → forestWeight rank trimmed < forestWeight rank forest) := by
  unfold propagate
  split
  · have checked := erase_progress forest state facts values represented
    exact ⟨_, checked.1, checked.2.1, fun index path _ => checked.2.2.1 index path, checked.2.2.2⟩
  · exact ⟨forest, represented, EqualityLeafProjectionSyntax.progress_refl _ _, fun _ _ endpoint => endpoint,
      fun different => False.elim (different rfl)⟩

end MicroCFTA.EqualityLeafProjectionRuntimeEmpty
