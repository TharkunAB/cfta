import MicroCFTA.EqualityLeafProjectionEditRelabel

/-!
# Physical target closures and finite leaf witnesses

A represented target compiles without allocation. The actual source edit
with retained physical targets therefore has the same complete run as the
finite-target edit in that cache and every valid cache extension.
-/
namespace MicroCFTA.EqualityLeafProjectionPhysicalTargets
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Tree Path Admissible)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers EqualityLeafProjectionEditAgreement EqualityLeafProjectionEditRelabel
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A closed target compiler performs no source requests before physical intersection. -/
theorem meet_closed (target : Leaf initial symbols) (physical value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey)
    (represented : Represents EqualityRawLeafCompiler.build (.leaf target) state physical) :
    run (EqualityRawLeafCompiler.meet target value) state = run (EqualityRawLeafProduct.intersect physical value) state := by
  change run (EqualityRawLeafCompiler.build target) state = (physical, state) at represented
  simp only [EqualityRawLeafCompiler.meet, EqualityLeafProjectionActualMeet.rawMeet, run_bind]
  change run (EqualityRawLeafProduct.intersect (run (EqualityRawLeafCompiler.build target) state).1 value)
    (run (EqualityRawLeafCompiler.build target) state).2 = _
  rw [represented]

/-- Closed target representation determines intersection agreement after cache growth. -/
theorem meet_agree (target : Leaf initial symbols) (physical value : Value (Fin symbols) ConstraintKey)
    (base : State (Fin symbols) ConstraintKey) (valid : Valid base)
    (represented : Represents EqualityRawLeafCompiler.build (.leaf target) base physical) :
    Agree base (EqualityRawLeafCompiler.meet target value) (EqualityRawLeafProduct.intersect physical value) := by
  intro state _ growth
  exact meet_closed target physical value state
    (EqualityLeafProjectionRepresentation.grows EqualityRawLeafCompiler.build (.leaf target) base state valid growth physical represented)

/-- Finite and physical edit payloads have exactly the same complete source run. -/
theorem edits_agree
    (edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey)))
    (base : State (Fin symbols) ConstraintKey) (valid : Valid base)
    (represented : ∀ path pair, (path, pair) ∈ edits → Represents EqualityRawLeafCompiler.build (.leaf pair.1) base pair.2)
    (value : Value (Fin symbols) ConstraintKey) :
    Agree base (edit EqualityRawLeafCompiler.meet (targets Prod.fst edits) value)
      (edit EqualityRawLeafProduct.intersect (targets Prod.snd edits) value) := by
  rw [edit_targets, edit_targets]
  apply edit_agree
  intro path pair member node
  exact meet_agree pair.1 pair.2 node base valid (represented path pair member)

/-- Retained physical target closures inherit exact recursive occurrence transport
when their finite witnesses are already represented in the input cache. -/
theorem physical_transport
    (tree : Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols))
    (edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey)))
    (admissible : Admissible (targets Prod.fst edits) tree)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (targetsRepresented : ∀ path pair, (path, pair) ∈ edits → Represents EqualityRawLeafCompiler.build (.leaf pair.1) state pair.2)
    (value : Value (Fin symbols) ConstraintKey) (represented : Represents EqualityRawLeafCompiler.build tree state value) :
    let actual := run (edit EqualityRawLeafProduct.intersect (targets Prod.snd edits) value) state
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents EqualityRawLeafCompiler.build
        (EqualityLeafProjectionSyntax.edit EqualityRawLeafInventory.intersect (targets Prod.fst edits) tree) after result := by
  have same := edits_agree edits state facts.coherent.valid targetsRepresented value state facts.coherent.valid (grows_refl state)
  have checked := EqualityLeafProjectionEditExact.raw_transport tree (targets Prod.fst edits) admissible state facts value represented
  rw [same] at checked
  exact checked

end MicroCFTA.EqualityLeafProjectionPhysicalTargets
