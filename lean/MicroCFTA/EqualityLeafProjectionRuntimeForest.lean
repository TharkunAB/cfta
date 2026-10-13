import MicroCFTA.EqualityLeafProjectionRuntimeEdit

/-!
# Runtime-cache witnesses for ordered forest workers

The actual child-list worker retains source order and uses its actual
output cache. Trimmed forest witnesses decrease the original occurrence
potential while preserving all selected endpoint positions.
-/
namespace MicroCFTA.EqualityLeafProjectionRuntimeForest
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionSyntax (Tree Path ChildAt Progress forestWeight)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers EqualityLeafProjectionRequireAvailability EqualityLeafProjectionEditAvailability
open EqualityLeafProjectionEditRelabel (targets)
open EqualityLeafProjectionTrim
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Ordinary membership gives the child worker's structural ordinary predicate. -/
theorem ordinary_children (values : List (Value Symbol Guard))
    (all : ∀ value ∈ values, EqualityLeafProjectionWorkers.Ordinary value) : OrdinaryChildren values := by
  induction values with
  | nil => trivial
  | cons value rest ih => exact ⟨all value (by simp), ih (fun other member => all other (by simp [member]))⟩

/-- A represented finite raw forest trims into the cache retaining all its physical children. -/
theorem forest_pullback
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (before after : State (Fin symbols) ConstraintKey) (beforeFacts : Facts before) (afterFacts : Facts after)
    (values : List (Value (Fin symbols) ConstraintKey)) (available : ∀ value ∈ values, Available before value)
    (represented : RepresentsForest build forest after values) :
    ∃ trimmed, TrimForest trimmed forest ∧ RepresentsForest build trimmed before values :=
  EqualityLeafProjectionTrimTransport.forest build forest (fun tree _ => EqualityLeafProjectionTrimExact.raw_pullback tree)
    before after beforeFacts afterFacts values available represented

/-- Simultaneous finite leaf targets give exact trimmed witnesses in the worker's actual cache. -/
theorem finite_edit_actual
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (edits : List (Path × Leaf initial symbols)) (index : Nat)
    (admissible : ∀ offset path target, ((index + offset) :: path, target) ∈ edits → ChildAt offset path forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (editChildren EqualityRawLeafCompiler.meet edits index values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      TrimForest trimmed (EqualityLeafProjectionSyntax.editChildren EqualityRawLeafInventory.intersect edits index forest) := by
  let actual := run (editChildren EqualityRawLeafCompiler.meet edits index values) state
  have input := forest_available build EqualityRawLeafCompiler.leaves_available forest state facts values represented
  have checked := editChildren_available EqualityRawLeafCompiler.meet EqualityRawLeafCompiler.meet_available edits index values state facts input
  have ordinary := compileForest_ordinary build EqualityRawLeafCompiler.leaves_available EqualityRawLeafCompiler.leaves_ordinary forest state facts
  rw [represented] at ordinary
  obtain ⟨results, returned⟩ := editChildren_returns EqualityRawLeafCompiler.meet edits index values (ordinary_children values ordinary) state
  have growth : Grows state actual.2 := (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2
  have laterOriginal := forest_grows build forest state actual.2 facts.coherent.valid growth values represented
  have closed : run (editChildren EqualityRawLeafCompiler.meet edits index values) actual.2 = (some results, actual.2) := by
    simpa only [returned] using replay (editChildren EqualityRawLeafCompiler.meet edits index values) state actual.2
      facts.coherent.valid (grows_refl _)
  obtain ⟨after, afterFacts, _, laterRep⟩ := EqualityLeafProjectionEditTransport.closed_children build EqualityRawLeafCompiler.meet
    EqualityRawLeafInventory.intersect forest (fun tree _ => EqualityLeafProjectionEditExact.raw_transport tree)
    edits index admissible actual.2 checked.1 values results laterOriginal closed
  obtain ⟨trimmed, removed, output⟩ := forest_pullback _ actual.2 after checked.1 afterFacts results (checked.2 results returned) laterRep
  exact ⟨checked.1, results, trimmed, returned, output, removed⟩

/-- Retained physical targets give the identical complete ordered child run. -/
theorem target_run
    (edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey)))
    (index : Nat) (values : List (Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : ∀ path pair, (path, pair) ∈ edits → Represents build (.leaf pair.1) state pair.2) :
    run (editChildren EqualityRawLeafCompiler.meet (targets Prod.fst edits) index values) state =
      run (editChildren EqualityRawLeafProduct.intersect (targets Prod.snd edits) index values) state := by
  rw [EqualityLeafProjectionEditRelabel.children_targets, EqualityLeafProjectionEditRelabel.children_targets]
  have localAgreement : ∀ path pair, (path, pair) ∈ edits → ∀ value,
      EqualityLeafProjectionEditAgreement.Agree state
        (EqualityRawLeafCompiler.meet pair.1 value) (EqualityRawLeafProduct.intersect pair.2 value) := by
    intro path pair member value
    exact EqualityLeafProjectionPhysicalTargets.meet_agree pair.1 pair.2 value state facts.coherent.valid (represented path pair member)
  have agreement := EqualityLeafProjectionEditAgreement.children_agree state
    (fun pair : Leaf initial symbols × Value (Fin symbols) ConstraintKey => EqualityRawLeafCompiler.meet pair.1)
    (fun pair : Leaf initial symbols × Value (Fin symbols) ConstraintKey => EqualityRawLeafProduct.intersect pair.2)
    edits localAgreement index values
  exact agreement state facts.coherent.valid (grows_refl state)

/-- Actual retained physical closures give a trimmed forest in the actual output cache. -/
theorem edit_actual
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey))) (index : Nat)
    (admissible : ∀ offset path target, ((index + offset) :: path, target) ∈ targets Prod.fst edits → ChildAt offset path forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (targetsRepresented : ∀ path pair, (path, pair) ∈ edits → Represents build (.leaf pair.1) state pair.2)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (editChildren EqualityRawLeafProduct.intersect (targets Prod.snd edits) index values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      TrimForest trimmed (EqualityLeafProjectionSyntax.editChildren EqualityRawLeafInventory.intersect (targets Prod.fst edits) index forest) := by
  have checked := finite_edit_actual forest (targets Prod.fst edits) index admissible state facts values represented
  rw [target_run edits index values state facts targetsRepresented] at checked
  exact checked

/-- Actual required child paths give a trimmed forest in the actual output cache. -/
theorem require_actual
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols))) (paths : List Path) (index : Nat)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (requireChildren paths index values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      TrimForest trimmed (EqualityLeafProjectionSyntax.requireChildren paths index forest) := by
  have input := forest_available build EqualityRawLeafCompiler.leaves_available forest state facts values represented
  have checked := requireChildren_available paths index values state facts input
  obtain ⟨after, results, afterFacts, _, returned, laterRep⟩ := EqualityLeafProjectionRequireTransport.children build
    EqualityRawLeafCompiler.leaves_available EqualityRawLeafCompiler.leaves_ordinary forest
    (fun tree _ => EqualityLeafProjectionRequireExact.raw_transport tree) paths index state facts values represented
  obtain ⟨trimmed, removed, output⟩ := forest_pullback _ _ after checked.1 afterFacts results (checked.2 results returned) laterRep
  exact ⟨checked.1, results, trimmed, returned, output, removed⟩

/-- A changed ordered physical identity list forces a strict occurrence-potential decrease. -/
theorem physical_strict
    (forest trimmed : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (work : Work (Fin symbols) ConstraintKey Result)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values results : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values)
    (output : RepresentsForest build trimmed (run work state).2 results)
    (progress : Progress (forestWeight rank) trimmed forest)
    (changed : results.map Value.referenceOf ≠ values.map Value.referenceOf) :
    forestWeight rank trimmed < forestWeight rank forest := by
  apply EqualityLeafProjectionSyntax.progress_strict _ _ _ progress
  intro same
  subst trimmed
  have earlier := forest_grows build forest state (run work state).2 facts.coherent.valid
    (InternedConstructorTemplates.run_correct work state facts.coherent.valid).2 values represented
  have sameValues : results = values := (Prod.mk.inj (output.symm.trans earlier)).1
  exact changed (congrArg (List.map Value.referenceOf) sameValues)

/-- Simultaneous forest editing preserves endpoints and strictly decreases rank on physical change. -/
theorem edit_progress
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (edits : List (Path × (Leaf initial symbols × Value (Fin symbols) ConstraintKey))) (index : Nat)
    (admissible : ∀ offset path target, ((index + offset) :: path, target) ∈ targets Prod.fst edits → ChildAt offset path forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (targetsRepresented : ∀ path pair, (path, pair) ∈ edits → Represents build (.leaf pair.1) state pair.2)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (editChildren EqualityRawLeafProduct.intersect (targets Prod.snd edits) index values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Progress (forestWeight rank) trimmed forest ∧
      (∀ offset path, ChildAt offset path forest → ChildAt offset path trimmed) ∧
      (results.map Value.referenceOf ≠ values.map Value.referenceOf → forestWeight rank trimmed < forestWeight rank forest) := by
  obtain ⟨checked, results, trimmed, returned, output, removed⟩ := edit_actual forest edits index admissible state facts targetsRepresented values represented
  have progress := EqualityLeafProjectionSyntax.progress_trans (forestWeight rank) forest _ trimmed
    (EqualityLeafProjectionSyntax.edit_children_progress rank EqualityRawLeafInventory.intersect EqualityRawLeafInventory.leaf_progress _ index forest)
    (EqualityLeafProjectionTrim.forest_progress rank removed)
  exact ⟨checked, results, trimmed, returned, output, progress,
    fun offset path endpoint => EqualityLeafProjectionTrim.childAt removed offset path
      (EqualityLeafProjectionSyntax.edit_children_leafAt _ _ index offset path forest endpoint),
    physical_strict forest trimmed _ state facts values results represented output progress⟩

/-- Required paths preserve all future endpoints and decrease rank on physical change. -/
theorem require_progress
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols))) (paths : List Path) (index : Nat)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (requireChildren paths index values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Progress (forestWeight rank) trimmed forest ∧
      (∀ offset path, ChildAt offset path forest → ChildAt offset path trimmed) ∧
      (results.map Value.referenceOf ≠ values.map Value.referenceOf → forestWeight rank trimmed < forestWeight rank forest) := by
  obtain ⟨checked, results, trimmed, returned, output, removed⟩ := require_actual forest paths index state facts values represented
  have progress := EqualityLeafProjectionSyntax.progress_trans (forestWeight rank) forest _ trimmed
    (EqualityLeafProjectionSyntax.require_children_progress rank paths index forest)
    (EqualityLeafProjectionTrim.forest_progress rank removed)
  exact ⟨checked, results, trimmed, returned, output, progress,
    fun offset path endpoint => EqualityLeafProjectionTrim.childAt removed offset path
      (EqualityLeafProjectionSyntax.require_children_leafAt paths index offset path forest endpoint),
    physical_strict forest trimmed _ state facts values results represented output progress⟩

end MicroCFTA.EqualityLeafProjectionRuntimeForest
