import MicroCFTA.EqualityLeafProjectionTrimExact
import MicroCFTA.EqualityLeafProjectionInvariant

/-!
# Runtime-cache witnesses for physical leaf edits and requirements

Each theorem executes the actual worker from the input cache. Trimming
returns a witness in its actual output cache. Later proof allocations do
not change runtime state. Physical changes force strict occurrence progress.
-/
namespace MicroCFTA.EqualityLeafProjectionRuntimeEdit
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionSyntax (Tree Path Admissible LeafAt Progress weight)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers EqualityLeafProjectionRequireAvailability EqualityLeafProjectionEditAvailability
open EqualityLeafProjectionEditRelabel (targets)
open EqualityLeafProjectionTrim
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Actual physical edit results reconstruct without allocation in the actual output cache. -/
theorem edit_actual
    (tree : Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols))
    (edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey)))
    (admissible : Admissible (targets Prod.fst edits) tree)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (targetsRepresented : ∀ path pair, (path, pair) ∈ edits → Represents build (.leaf pair.1) state pair.2)
    (value : Value (Fin symbols) ConstraintKey) (represented : Represents build tree state value) :
    let actual := run (edit EqualityRawLeafProduct.intersect (targets Prod.snd edits) value) state
    Facts actual.2 ∧ ∃ result trimmed, actual.1 = some result ∧
      Represents build trimmed actual.2 result ∧
      Trim trimmed (EqualityLeafProjectionSyntax.edit EqualityRawLeafInventory.intersect (targets Prod.fst edits) tree) := by
  have input := EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available tree state facts value represented
  have checked := edit_available EqualityRawLeafCompiler.meet EqualityRawLeafCompiler.meet_available (targets Prod.fst edits) value state facts input
  have same := EqualityLeafProjectionPhysicalTargets.edits_agree edits state facts.coherent.valid targetsRepresented value
    state facts.coherent.valid (grows_refl state)
  unfold Checked at checked
  rw [same] at checked
  obtain ⟨after, result, afterFacts, _, returned, laterRep⟩ := EqualityLeafProjectionPhysicalTargets.physical_transport
    tree edits admissible state facts targetsRepresented value represented
  obtain ⟨trimmed, removed, actualRep⟩ := EqualityLeafProjectionTrimExact.raw_pullback _ _ after checked.1 afterFacts result
    (checked.2 result returned) laterRep
  exact ⟨checked.1, result, trimmed, returned, actualRep, removed⟩

/-- Required-path filtering also reconstructs in the actual runtime cache. -/
theorem require_actual
    (tree : Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)) (paths : List Path)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (value : Value (Fin symbols) ConstraintKey) (represented : Represents build tree state value) :
    let actual := run (require paths value) state
    Facts actual.2 ∧ ∃ result trimmed, actual.1 = some result ∧ Represents build trimmed actual.2 result ∧
      Trim trimmed (EqualityLeafProjectionSyntax.require paths tree) := by
  have input := EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available tree state facts value represented
  have checked := require_available paths value state facts input
  obtain ⟨after, result, afterFacts, _, returned, laterRep⟩ := EqualityLeafProjectionRequireExact.raw_transport tree paths state facts value represented
  obtain ⟨trimmed, removed, actualRep⟩ := EqualityLeafProjectionTrimExact.raw_pullback _ _ after checked.1 afterFacts result
    (checked.2 result returned) laterRep
  exact ⟨checked.1, result, trimmed, returned, actualRep, removed⟩

/-- A changed physical result excludes equal occurrence weight in the exact runtime cache. -/
theorem physical_strict
    (tree trimmed : Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols))
    (work : Work (Fin symbols) ConstraintKey Result)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (value result : Value (Fin symbols) ConstraintKey) (represented : Represents build tree state value)
    (output : Represents build trimmed (run work state).2 result)
    (progress : Progress (weight rank) trimmed tree) (changed : result.referenceOf ≠ value.referenceOf) :
    weight rank trimmed < weight rank tree := by
  apply EqualityLeafProjectionSyntax.progress_strict _ _ _ progress
  intro same
  subst trimmed
  have earlier := EqualityLeafProjectionRepresentation.grows build tree state (run work state).2 facts.coherent.valid
    (InternedConstructorTemplates.run_correct work state facts.coherent.valid).2 value represented
  have values : result = value := by
    have exactRun := output.symm.trans earlier
    exact (Prod.mk.inj exactRun).1
  exact changed (congrArg Value.referenceOf values)

/-- Physical edits supply progress, invariant endpoints, and a strict bound when identity changes. -/
theorem edit_progress
    (tree : Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols))
    (edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey)))
    (admissible : Admissible (targets Prod.fst edits) tree)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (targetsRepresented : ∀ path pair, (path, pair) ∈ edits → Represents build (.leaf pair.1) state pair.2)
    (value : Value (Fin symbols) ConstraintKey) (represented : Represents build tree state value) :
    let actual := run (edit EqualityRawLeafProduct.intersect (targets Prod.snd edits) value) state
    Facts actual.2 ∧ ∃ result trimmed, actual.1 = some result ∧ Represents build trimmed actual.2 result ∧
      Progress (weight rank) trimmed tree ∧ (∀ path, LeafAt path tree → LeafAt path trimmed) ∧
      (result.referenceOf ≠ value.referenceOf → weight rank trimmed < weight rank tree) := by
  obtain ⟨checked, result, trimmed, returned, output, removed⟩ := edit_actual tree edits admissible state facts targetsRepresented value represented
  have progress := EqualityLeafProjectionSyntax.progress_trans (weight rank) tree _ trimmed
    (EqualityLeafProjectionSyntax.edit_progress rank EqualityRawLeafInventory.intersect EqualityRawLeafInventory.leaf_progress _ tree)
    (EqualityLeafProjectionTrim.progress rank removed)
  exact ⟨checked, result, trimmed, returned, output, progress,
    fun path endpoint => EqualityLeafProjectionTrim.leafAt removed path
      (EqualityLeafProjectionSyntax.edit_leafAt _ _ path tree endpoint),
    physical_strict tree trimmed _ state facts value result represented output progress⟩

/-- Required paths supply the same runtime progress and physical identity bound. -/
theorem require_progress
    (tree : Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)) (paths : List Path)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (value : Value (Fin symbols) ConstraintKey) (represented : Represents build tree state value) :
    let actual := run (require paths value) state
    Facts actual.2 ∧ ∃ result trimmed, actual.1 = some result ∧ Represents build trimmed actual.2 result ∧
      Progress (weight rank) trimmed tree ∧ (∀ path, LeafAt path tree → LeafAt path trimmed) ∧
      (result.referenceOf ≠ value.referenceOf → weight rank trimmed < weight rank tree) := by
  obtain ⟨checked, result, trimmed, returned, output, removed⟩ := require_actual tree paths state facts value represented
  have progress := EqualityLeafProjectionSyntax.progress_trans (weight rank) tree _ trimmed
    (EqualityLeafProjectionSyntax.require_progress rank paths tree) (EqualityLeafProjectionTrim.progress rank removed)
  exact ⟨checked, result, trimmed, returned, output, progress,
    fun path endpoint => EqualityLeafProjectionTrim.leafAt removed path (EqualityLeafProjectionSyntax.require_leafAt paths path tree endpoint),
    physical_strict tree trimmed _ state facts value result represented output progress⟩

end MicroCFTA.EqualityLeafProjectionRuntimeEdit
