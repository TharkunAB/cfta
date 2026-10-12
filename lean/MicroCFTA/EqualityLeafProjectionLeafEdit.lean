import MicroCFTA.EqualityLeafProjectionNullaryEdit

/-!
# Exact finite raw leaf edits

Root edits use the source whole-node identity and Cartesian intersection.
Descendant-only edits replay the unchanged nullary leaf. EmptyNode returns
immediately; finite proof preparation represents its absorbing leaf result.
-/
namespace MicroCFTA.EqualityLeafProjectionLeafEdit
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionSyntax (Path atRoot)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionLeafCache (ConstraintKey)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Actual raw Cartesian construction against an empty right leaf returns EmptyNode. -/
theorem intersect_empty (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    (run (EqualityRawLeafProduct.intersect value .empty) state).1 = .empty := by
  unfold EqualityRawLeafProduct.intersect
  split
  · rename_i same
    have empty : value = .empty := (reference_empty value).mp same
    subst value
    rfl
  · have noPairs : EqualityRawLeafProduct.cross ((nodeEdges value).map EqualityRawLeafProduct.declaration) [] = [] := by
      unfold EqualityRawLeafProduct.cross
      rw [SymbolicHashJoin.hashJoin_exact]
      apply List.flatMap_eq_nil_iff.mpr
      intro row _
      simp
    change (run (EqualityRawLeafConstruction.build (EqualityRawLeafProduct.cross
      ((nodeEdges value).map EqualityRawLeafProduct.declaration) [])) state).1 = .empty
    rw [noPairs]
    simp [EqualityRawLeafConstruction.build, EqualityRawLeafConstruction.requests,
      sequence, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds, run_bind, run]

/-- Building a target does not change the source's empty intersection result. -/
theorem meet_empty (target : EqualityRawLeafInventory.Leaf initial symbols) (state : State (Fin symbols) ConstraintKey) :
    (run (EqualityRawLeafCompiler.meet target .empty) state).1 = .empty := by
  simp only [EqualityRawLeafCompiler.meet, EqualityLeafProjectionActualMeet.rawMeet, run_bind, intersect_empty]

/-- Every actual finite raw leaf edit gets the exact abstract leaf intersection
representation after finite later preparation. No leaf edit law is assumed. -/
theorem raw_leaf_edit
    (before : EqualityRawLeafInventory.Leaf initial symbols)
    (edits : List (Path × EqualityRawLeafInventory.Leaf initial symbols))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (value : Value (Fin symbols) ConstraintKey)
    (represented : Represents EqualityRawLeafCompiler.build (.leaf before) state value) :
    let actual := run (edit EqualityRawLeafCompiler.meet edits value) state
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents EqualityRawLeafCompiler.build
        (.leaf (match atRoot edits with | none => before | some target => EqualityRawLeafInventory.intersect target before)) after result := by
  cases selected : atRoot edits with
  | none =>
      have unchanged := EqualityLeafProjectionNullaryEdit.represented_raw_below before EqualityRawLeafCompiler.meet edits selected value state facts represented
      refine ⟨state, value, facts, ?_, ?_, ?_⟩
      · rw [unchanged]
        exact grows_refl state
      · exact congrArg (fun pair : Option (Value (Fin symbols) ConstraintKey) × State (Fin symbols) ConstraintKey => pair.1) unchanged
      · simpa only [selected] using represented
  | some target =>
      let actualMeet := run (EqualityRawLeafCompiler.meet target value) state
      let prepared := run (EqualityRawLeafCompiler.build (EqualityRawLeafInventory.intersect target before)) actualMeet.2
      have completed := EqualityRawLeafCompiler.represented_meet target before state value facts represented
      have root := (EqualityRawLeafUnion.represented_fields before value state facts represented).2.2.1
      cases edits with
      | nil => simp [atRoot] at selected
      | cons first rest =>
          cases value with
          | empty =>
              refine ⟨prepared.2, .empty, completed.1, ?_, ?_, ?_⟩
              · simpa only [edit_empty, run] using grows_trans
                  (InternedConstructorTemplates.run_correct (EqualityRawLeafCompiler.meet target .empty) state facts.coherent.valid).2 completed.2.1
              · simp only [edit_empty, run]
              · have output := completed.2.2
                rw [meet_empty] at output
                simpa only [selected] using output
          | reference | union | mu => simp only [EqualityLeafProjectionUnion.OrdinaryRoot] at root
          | node entry edges depth free =>
              refine ⟨prepared.2, actualMeet.1, completed.1, ?_, ?_, ?_⟩
              · simpa only [edit, selected, run_bind, run] using completed.2.1
              · simp only [edit, selected, run_bind, run]
                rfl
              · simpa only [selected] using completed.2.2

end MicroCFTA.EqualityLeafProjectionLeafEdit
